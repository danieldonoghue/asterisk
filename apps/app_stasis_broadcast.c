/*
 * Asterisk -- An open source telephony toolkit.
 *
 * Copyright (C) 2025, Aurora Innovation AB
 *
 * Daniel Donoghue <daniel.donoghue@aurorainnovation.com>
 *
 * See http://www.asterisk.org for more information about
 * the Asterisk project. Please do not directly contact
 * any of the maintainers of this project for assistance;
 * the project provides a web site, mailing lists and IRC
 * channels for your use.
 *
 * This program is free software, distributed under the terms of
 * the GNU General Public License Version 2. See the LICENSE file
 * at the top of the source tree.
 */

/*! \file
 *
 * \brief Stasis broadcast dialplan application
 *
 * \author Daniel Donoghue <daniel.donoghue@aurorainnovation.com>
 */

/*** MODULEINFO
	<depend type="module">res_stasis</depend>
	<depend type="module">res_stasis_broadcast</depend>
	<support_level>extended</support_level>
 ***/

#include "asterisk.h"

#include "asterisk/app.h"
#include "asterisk/module.h"
#include "asterisk/pbx.h"
#include "asterisk/stasis_app_broadcast.h"
#include "asterisk/stasis_app_impl.h"

/*** DOCUMENTATION
	<application name="StasisBroadcast" language="en_US">
		<since>
			<version>TBD</version>
		</since>
		<synopsis>Broadcast a channel to multiple ARI applications for claiming,
		then hand control to the winning application.</synopsis>
		<syntax>
			<parameter name="timeout">
				<para>Timeout in milliseconds to wait for a claim.</para>
				<para>Valid range: 0 to 60000ms</para>
				<para>Default: 500ms</para>
			</parameter>
			<parameter name="app_filter">
				<para>Regular expression to filter which ARI applications
				receive the broadcast. Only applications with names matching
				the regex will be notified.</para>
				<para>Because options are comma-delimited, commas cannot
				appear in the regex pattern. Use character classes
				(e.g. <literal>[,]</literal>) if a literal comma is
				needed, or omit the filter and handle selection in the
				ARI application.</para>
				<para>Default: all connected applications</para>
			</parameter>
			<parameter name="args">
				<para>Optional colon-delimited arguments passed to the winning
				application via the <literal>StasisStart</literal> event. These
				are equivalent to the extra arguments in <literal>Stasis()</literal>.</para>
				<para>Example: <literal>args=sales:priority-high</literal></para>
			</parameter>
			<parameter name="notify_claimed">
				<para>Whether to send a <literal>CallClaimed</literal> event to
				ARI applications when a channel is claimed.</para>
				<para>When enabled, the <literal>CallClaimed</literal> event is
				sent only to applications that matched the
				<replaceable>app_filter</replaceable> (or all applications if no
				filter was set).</para>
				<para>Disabled by default to minimise WebSocket traffic under
				high load. Losing claimants already receive a
				<literal>409</literal> HTTP response.</para>
				<para>Default: no</para>
			</parameter>
		</syntax>
		<description>
			<para>Broadcasts the incoming channel to all connected ARI applications
			(or a filtered subset) via a <literal>CallBroadcast</literal> event.
			ARI applications can respond with a claim request. The first application
			to claim the channel wins, and subsequent claims are rejected.</para>
			<para>If an application claims the channel within the timeout, the channel
			is automatically placed under Stasis control with the winning application,
			exactly as if <literal>Stasis(winner_app)</literal> had been called.
			The winning application receives a <literal>StasisStart</literal> event
			and has full channel control until it calls <literal>continue</literal>
			or the channel hangs up.</para>
			<para>If no application claims the channel within the timeout, control
			returns to the dialplan immediately, allowing fallback handling.</para>
			<para>This application will set the following channel variables:</para>
			<variablelist>
				<variable name="STASISSTATUS">
					<value name="SUCCESS">
						An application claimed the channel and the Stasis
						session completed without failures.
					</value>
					<value name="FAILED">
						An application claimed the channel but a failure
						occurred when executing the Stasis application.
					</value>
					<value name="TIMEOUT">
						No application claimed the channel within the
						timeout period.
					</value>
				</variable>
			</variablelist>
			<example>
			; Broadcast with default timeout (500ms) to all apps
			; Channel automatically enters Stasis with the winner
			exten => _X.,1,StasisBroadcast()
			 same => n,GotoIf($["${STASISSTATUS}"="TIMEOUT"]?no_route)
			 same => n,Hangup()
			 same => n(no_route),Playback(sorry-no-agent)
			 same => n,Hangup()
			</example>
			<example>
			; Broadcast with args passed to the winning application
			exten => _X.,1,StasisBroadcast(timeout=2000,app_filter=^ivr-.*,args=sales:priority-high)
			 same => n,GotoIf($["${STASISSTATUS}"="TIMEOUT"]?no_route)
			 same => n,Hangup()
			 same => n(no_route),Playback(sorry-no-agent)
			 same => n,Hangup()
			</example>
		</description>
	</application>
 ***/

/*! \brief Dialplan application name */
static const char *app = "StasisBroadcast";

/*! \brief Default timeout in milliseconds */
#define DEFAULT_TIMEOUT_MS 500

/*! \brief Maximum timeout in milliseconds */
#define MAX_TIMEOUT_MS 60000

/*! \brief Maximum number of Stasis arguments */
#define MAX_STASIS_ARGS 128

/*! \brief Maximum number of comma-separated key=value options */
#define MAX_OPTIONS 10

/*! \brief StasisBroadcast dialplan application callback */
static int stasis_broadcast_exec(struct ast_channel *chan, const char *data)
{
	char *parse = NULL;
	char *options_str = NULL;
	int timeout_ms = DEFAULT_TIMEOUT_MS;
	const char *app_filter = NULL;
	const char *stasis_args_raw = NULL;
	unsigned int flags = STASIS_BROADCAST_FLAG_SUPPRESS_CLAIMED;
	char *winner = NULL;
	int result = 0;
	int stasis_argc = 0;
	char *stasis_argv[MAX_STASIS_ARGS];

	AST_DECLARE_APP_ARGS(args,
		AST_APP_ARG(options);
	);

	AST_DECLARE_APP_ARGS(options,
		AST_APP_ARG(option)[MAX_OPTIONS];
	);

	ast_assert(chan != NULL);

	/* Initialize channel variable */
	pbx_builtin_setvar_helper(chan, "STASISSTATUS", "");

	/* Parse arguments if provided */
	if (!ast_strlen_zero(data)) {
		parse = ast_strdupa(data);
		AST_STANDARD_APP_ARGS(args, parse);

		if (!ast_strlen_zero(args.options)) {
			int i;
			options_str = ast_strdupa(args.options);
			AST_STANDARD_APP_ARGS(options, options_str);

			/* Parse key=value options */
			for (i = 0; i < options.argc; i++) {
				char *key = options.option[i];
				char *val = strchr(key, '=');

				if (val) {
					*val++ = '\0';
					ast_strip(key);
					ast_strip(val);

					if (!strcasecmp(key, "timeout")) {
						if (sscanf(val, "%d", &timeout_ms) != 1 || timeout_ms < 0 || timeout_ms > MAX_TIMEOUT_MS) {
							ast_log(LOG_WARNING,
								"Invalid timeout value '%s' (must be 0-%dms), using default %dms\n",
								val, MAX_TIMEOUT_MS, DEFAULT_TIMEOUT_MS);
							timeout_ms = DEFAULT_TIMEOUT_MS;
						}
					} else if (!strcasecmp(key, "app_filter")) {
						app_filter = val;
					} else if (!strcasecmp(key, "args")) {
						stasis_args_raw = val;
					} else if (!strcasecmp(key, "notify_claimed")) {
						if (ast_true(val)) {
							flags &= ~STASIS_BROADCAST_FLAG_SUPPRESS_CLAIMED;
						}
					} else {
						ast_log(LOG_WARNING, "Unknown option '%s'\n", key);
					}
				}
			}
		}
	}

	/*
	 * Parse colon-delimited Stasis arguments.  stasis_argv[] holds
	 * pointers into the stack-allocated args_copy buffer.  This is
	 * safe because stasis_app_exec is called within this same
	 * function scope so the stack frame remains alive.
	 */
	if (!ast_strlen_zero(stasis_args_raw)) {
		char *args_copy = ast_strdupa(stasis_args_raw);
		char *arg;

		while ((arg = strsep(&args_copy, ":")) != NULL && stasis_argc < MAX_STASIS_ARGS) {
			stasis_argv[stasis_argc++] = arg;
		}
	}

	ast_verb(3, "Broadcasting channel %s (timeout=%dms, filter=%s, args=%d)\n",
		ast_channel_name(chan), timeout_ms, app_filter ? app_filter : "none",
		stasis_argc);

	/* Start the broadcast */
	result = stasis_app_broadcast_channel(chan, timeout_ms, app_filter, flags);
	if (result != 0) {
		ast_log(LOG_ERROR, "Failed to broadcast channel %s (return code: %d)\n",
			ast_channel_name(chan), result);
		pbx_builtin_setvar_helper(chan, "STASISSTATUS", "FAILED");
		return 0;
	}

	/* Wait for a claim.  A late claim can arrive between the timeout
	 * expiring and our cleanup call, so always check for a winner
	 * regardless of the wait result. */
	stasis_app_broadcast_wait(chan, timeout_ms);
	winner = stasis_app_broadcast_winner(ast_channel_uniqueid(chan));

	if (winner) {
		int ret;

		ast_verb(3, "Channel %s claimed by %s, entering Stasis\n",
			ast_channel_name(chan), winner);

		/* Defer cleanup until after Stasis so concurrent claimants can still
		 * find the context (with claimed=1) and receive 409 Conflict instead
		 * of 404 Not Found. */
		ret = stasis_app_exec(chan, winner, stasis_argc, stasis_argv);
		ast_free(winner);

		/* Clean up now that the Stasis session has ended */
		stasis_app_broadcast_cleanup(ast_channel_uniqueid(chan));

		if (ret) {
			pbx_builtin_setvar_helper(chan, "STASISSTATUS", "FAILED");
			if (ast_check_hangup(chan)) {
				return -1;
			}
		} else {
			pbx_builtin_setvar_helper(chan, "STASISSTATUS", "SUCCESS");
		}
	} else {
		/* No winner: clean up immediately, nothing to race against */
		stasis_app_broadcast_cleanup(ast_channel_uniqueid(chan));
		ast_verb(3, "Channel %s not claimed within timeout\n",
			ast_channel_name(chan));
		pbx_builtin_setvar_helper(chan, "STASISSTATUS", "TIMEOUT");
	}

	return 0;
}

static int load_module(void)
{
	return ast_register_application_xml(app, stasis_broadcast_exec);
}

static int unload_module(void)
{
	return ast_unregister_application(app);
}

AST_MODULE_INFO(ASTERISK_GPL_KEY, AST_MODFLAG_DEFAULT,
	"Stasis application broadcast",
	.support_level = AST_MODULE_SUPPORT_EXTENDED,
	.load = load_module,
	.unload = unload_module,
	.requires = "res_stasis,res_stasis_broadcast",
);

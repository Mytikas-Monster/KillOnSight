# KillOnSight

## KILL ON SIGHT


`/kos` opens the window (or minimap button). Shared kill list + death feed: enemy, victim, when, last known location.

RULE: a name or "pending job" is NOT a bounty. Flat 3g. 
The addon never moves gold; a bounty is live only when the guild bank's own balance rises by the deposit.

Fund: right-click a name (or /kos bounty <name> / Fund), open the bank once, deposit 3g. Live job is announced; part payments add up.
Payout: killer gets 70%, guild keeps 30%. Someone at the bank pays by hand, then click Paid. 
Unclaimed money returns to the payer after 7 days by hand (/kos refunddays <n>, 0=never). BGs/arenas ignored.

Addon-only map/minimap pins expire 30 min after sighting; live bounties get a nameplate badge.
Timed addon chat is blocked here, so officer reminders are one-click: /kos officers.

```
Commands: /kos
 add <name> [gold]
 bounty <name>
 fund <name>
 deposited
 paid <name>
 refund <name>
 handed <name>
 owed
 officers
 where [name]
 pins
 kills [mine]
 remove <name>
 reward
 cut
 refunddays
 list
 status
 bank
 sync
 announce
 share
 notices
 minimap
 reset
 recap
```

Defaults: 3g flat, 30% bank, 7 days.

/kos reward/cut/refunddays are per character.

One-time rules popup on first login must be acknowledged.
Install + share the board.

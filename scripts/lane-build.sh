#!/usr/bin/env bash
# Lane build throttle. Usage, from a worktree root:  bash scripts/lane-build.sh <Module> [<Module> ...]
# Two build slots are shared by every lane on this machine (the PC has 16 GB and only a few GB free);
# the script takes a slot, waits until at least 2.5 GB of memory is free, runs `lake build`, and
# releases the slot. Never call `lake build` or `lean` directly from a lane.
LOCKDIR=/c/GitHub_Files/Claude-Repos/sperner-t7-lean/.lanes-lock
mkdir -p "$LOCKDIR"
# a slot older than 25 minutes belongs to a dead lane
find "$LOCKDIR" -maxdepth 1 -mindepth 1 -name 'slot*' -mmin +25 -exec rmdir {} \; 2>/dev/null
slot=""
for _ in $(seq 1 720); do
  for s in slot1 slot2; do
    if mkdir "$LOCKDIR/$s" 2>/dev/null; then slot="$s"; break; fi
  done
  [ -n "$slot" ] && break
  sleep 5
done
if [ -z "$slot" ]; then echo "lane-build: no build slot after 60 minutes"; exit 2; fi
trap 'rmdir "$LOCKDIR/$slot" 2>/dev/null' EXIT
free=0
for _ in $(seq 1 90); do
  free=$(timeout 60 powershell.exe -NoProfile -Command "[math]::Round((Get-CimInstance Win32_OperatingSystem).FreePhysicalMemory/1MB,2)" 2>/dev/null | tr -d '\r')
  [ -z "$free" ] && free=0
  if awk "BEGIN{exit !($free >= 2.5)}"; then break; fi
  echo "lane-build: free memory $free GB < 2.5 GB; waiting"; sleep 15
done
echo "lane-build: $slot, free $free GB: lake build $*"
lake build "$@"
status=$?
echo "lane-build: exit $status"
exit $status

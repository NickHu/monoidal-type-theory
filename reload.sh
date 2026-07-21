#!/bin/sh
f="$1"
printf 'IOTCM "%s" None Indirect (Cmd_load "%s" [])\n' "$f" "$f" | agda --interaction-json 2>&1 | jq -R 'fromjson? // empty' | jq -rc 'select(.info.kind=="AllGoalsWarnings") | .info.visibleGoals[]? | "L\(.constraintObj.range[0].start.line): \(.type)"' 2>/dev/null

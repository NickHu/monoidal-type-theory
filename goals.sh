#!/bin/bash
f="$1"
printf 'IOTCM "%s" None Indirect (Cmd_load "%s" [])\n' "$f" "$f" | agda --interaction-json 2>&1 | jq -rc 'select(.kind=="DisplayInfo" and .info.kind=="AllGoalsWarnings") | .info.visibleGoals[]? | "\(.constraintObj.id) @ \(.constraintObj.range[0].start.line):\(.constraintObj.range[0].start.col)  ::  \(.type)"' 2>/dev/null

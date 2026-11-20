#!/usr/bin/env bash
# Every expected failure in src/tests.ts names an open issue. Fails if one of
# the issues named there is closed, or is still a placeholder (#TBD-...).
# Needs gh, authenticated (in CI, GH_TOKEN).
cd "$(dirname "$0")" || exit 2
status=0
for ref in $(grep -oP '(?<![\w-])([\w.-]+/[\w.-]+)?#(\d+|TBD-[\w-]+)' src/tests.ts | sort -u); do
  repo=${ref%%#*}
  num=${ref#*#}
  if [[ $num == TBD-* ]]; then
    echo "$ref: placeholder, file the issue and replace it with the issue number"
    status=1
    continue
  fi
  state=$(gh issue view "$num" -R "${repo:-peregrine-project/peregrine-tool}" --json state -q .state) || { status=1; continue; }
  echo "$ref: $state"
  [[ $state == OPEN ]] || status=1
done
exit $status

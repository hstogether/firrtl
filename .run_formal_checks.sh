#!/usr/bin/env bash
set -e
# Run formal check only for PRs
if [ $TRAVIS_PULL_REQUEST = "false" ]; then
    echo "Not a pull request, no formal check"
    exit 0
elif [[ $TRAVIS_COMMIT_MESSAGE == *"[skip formal checks]"* ]]; then
    echo "Commit message says to skip formal checks"
    exit 0
else
    # $TRAVIS_BRANCH is branch targeted by PR
    # Travis does a shallow clone, checkout PR target so that we have it
    # THen return to previous branch so HEAD points to the commit we're testing
    git remote set-branches origin $TRAVIS_BRANCH && git fetch
    git checkout $TRAVIS_BRANCH
    git checkout -
    ./scripts/formal_equiv.sh HEAD $TRAVIS_BRANCH Rob
    echo "Done with formal_equiv!"
fi

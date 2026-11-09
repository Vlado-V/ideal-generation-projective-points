#!/bin/sh
set -eu
cd "$(dirname "$0")"
"${LAKE:-lake}" --wfail build
"${LAKE:-lake}" env lean -DwarningAsError=true Audit.lean

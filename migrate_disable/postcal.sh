#!/bin/bash

set -e

SPEC=$1
shift

grep -q -e "--algorithm" $SPEC.tla && pluscal -nocfg $SPEC.tla | tee $SPEC.log
if grep -q -e "^\s*ProcessEnabled(self)\s*==" $SPEC.tla; then
	sed -i -e 's%pc\[self\] = ".*"$%& /\\\ ProcessEnabled(self)%' $SPEC.tla
fi

tlc -workers $(nproc) $@ $SPEC.tla | tee -a $SPEC.log

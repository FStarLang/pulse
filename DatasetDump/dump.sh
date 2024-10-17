git clean -fdx lib;

OTHERFLAGS='--admit_smt_queries true' make -j12 boot-checker;

OTHERFLAGS='--ext pulse:dataset=1' make -j1 | tee DatasetDump/dump.dataset.log;
COQMAKEFILE ?= Makefile.coq

# Inner make is forced to -j1 because coq_makefile (Rocq 9.0) does not
# order COQNATIVE artifact dependencies across files: the post-pass that
# generates X.coq-native imports the .cmxs of X's dependencies, but those
# may not yet exist when X's COQNATIVE rule fires under -j>1, producing
# spurious "Unbound module" errors. Sequential build of this project is
# ~14s, so the parallelism loss is acceptable. Override with JOBS=N to
# experiment, or run `make -f Makefile.coq -jN` directly at your own risk.
JOBS ?= 1

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) -j$(JOBS)

$(COQMAKEFILE): _CoqProject
	coq_makefile -f _CoqProject -o $(COQMAKEFILE)

clean: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) clean
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

.PHONY: all clean

-------------------------------------------------------------------------------

This is an archival copy of the [original page](http://web.archive.org/web/20161011094126/https://bitbucket.org/robsimmons/constructive-provability-logic/wiki/Home).

-------------------------------------------------------------------------------


# Constructive Provability Logic

This repository collects the code (currently all in Agda) for "Constructive Provability Logic," a research project by [Robert J. Simmons](http://www.cs.cmu.edu/~rjsimmon/) and [Bernardo Toninho](http://www.cs.cmu.edu/~btoninho/).

## Principles of Constructive Provability Logic

Tech report, December 2010. ([paper and code](http://reports-archive.adm.cs.cmu.edu/anon/2010/abstracts/10-151.html) ([repository tag "2010-tech-report"](https://github.com/mietek/constructive-provability-logic/tree/2010-tech-report))

The directory Accessibility introduces converse well-founded accessibility relations and contexts (lists) indexed by a converse well-founded accessibility relation, and the directory MinimalCPL describes the formalization and metatheory of a minimal fragment of constructive provability logic as discussed in the tech report.

## Constructive Provability Logic

Submitted, January 2011. ([submitted version](http://ctp.di.fct.unl.pt/~btoninho/imla11.pdf)) ([repository tag "2011-imla-submission"](https://github.com/mietek/constructive-provability-logic/tree/2011-imla-submission))

In addition to minor updates to the minimal CPL discussed in the tech report, as well as two variants of intuitionistic constructive provability logic (the "tethered" variant is in the directory IntuitionisticCPL, and the "de-tethered" variant is in the directory DetetheredCPL). The proofs of the theorems in Section 3 can all be found in [TetheredCPL/Axioms.agda](TetheredCPL/Axioms.agda) and [DetetheredCPL/Axioms.agda](DetetheredCPL/Axioms.agda), but the proofs of the theorems in Section 2 that deal with the metatheory of __CPL__ and __CPL*__ are a bit scattered; you can find them by clicking these links:

- Theorem 2.1, Weakening in __CPL__ - [here](TetheredCPL/Sequent.agda#L21) and [here](TetheredCPL/Sequent.agda#L108).
- Theorem 2.1, Identity in __CPL__ - [here](TetheredCPL/Sequent.agda#L156).
- Theorem 2.1, Cut in __CPL__ - [here](TetheredCPL/Sequent.agda#L123).
- Theorem 2.2, Weakening in __CPL*__ - proof [here](DetetheredCPL/SequentMetatheory/Core.agda#L90) and [here](DetetheredCPL/SequentMetatheory/Core.agda#L126), exported [here](DetetheredCPL/Sequent.agda#L34).
- Theorem 2.2, Identity in __CPL*__ - proof [here](DetetheredCPL/SequentMetatheory/Core.agda#L76), exported [here](DetetheredCPL/Sequent.agda#L25).
- Theorem 2.2, Cut in __CPL*__ - proof [here](DetetheredCPL/SequentMetatheory/Cut.agda#L32), exported [here](DetetheredCPL/Sequent.agda#L28). An unknown performance issue in Agda means that, even with the termination checker disabled, this proof takes about half an hour to compile. As long as the computational content of cut admissibility is not needed, the file [CutAxiom.agda](DetetheredCPL/SequentMetatheory/CutAxiom.agda) can be used. To add the real cut theorem to the code path, uncomment [this line](DetetheredCPL/SequentMetatheory/PostCut.agda#L13) and comment the following line.
- Theorem 2.2, Decut in __CPL*__ - proof [here](DetetheredCPL/SequentMetatheory/PreCut.agda#L22) and [here](DetetheredCPL/SequentMetatheory/PreCut.agda#L124), exported [here](DetetheredCPL/Sequent.agda#L31).

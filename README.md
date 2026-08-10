# Formal Repository for "Formalizations of Relational and Substantival Time Theories and Their Consistency with More General Theories of Time"

## Overview

This repository serves the primary purpose of providing verifiable proofs (via Lean 4) for several theorems which are used in the paper "Formalizations of Relational and Substantival Time Theories and Their Consistency with More General Theories of Time." In the folder *Verification*, the following files are, upon the completion of this project, readily available:

* `defs_alg.lean` & `proofs_alg.lean` conjunctly cover both the definitions and a few basic theorems relating to the "Observer Algebras" (formally referred to as "OT" to reference the axioms of an Observer Algebra) discussed in the paper. Several of the theorems proved in `proofs_alg.lean` will be in reference to the proofs in `proofs_timeHT.lean* for reasons which are made clear in the paper.
* `defs_timeB.lean` & `proofs_timeB.lean` conjunctly cover both the definitions and a few basic theorems relating to the common theory (denoted simply by "B") which is shared by both RT and ST ("RT" and "ST" meaning the formalized relational time and substantival time axioms used in this paper repsecitvely). These files will be referenced constantly in `defs_timeRT.lean`, `defs_timeST.lean`, `proofs_timeRT.lean`, and `proofs_timeST.lean`, since B serves as the theory which both formal theories must model in any of their models.
* `defs_timeHT.lean` & `proofs_timeHT.lean` conjunctly cover both the definitions and several basic theorems relating to the Hierarchy of Timelines (HT) theory of time. This serves as the theory which, when also given the additional axioms of the Observer Algebras, will be proved to satisyf both ST and RT in at least one of its models.
* `defs_timeRT.lean`, `defs_timeST.lean`, `proofs_timeRT.lean`, & `proofs_timeST.lean` conjunctly cover the definitions of the formalized relational and substantival time theories (RT and ST, respectively) along with a few relevant theorems for each theory.
* `CentralTheorems/modelsHTOT.lean` will provide the primary model of HT + OT that will be shown to satisfy both RT and ST.
* `CentralTheorems/modelsRT.lean` will provide a model of RT in isolation (if necessary, though this is subject to change depending on the needs of the paper) along with a demonstration that RT's axioms are satisfied by the model provided in `CentralTheorems/modelsHTOT.lean`.
* `CentralTheorems/modelsST.lean` will provide a model of ST in isolation (if necessary, though this is subject to change depending on the needs of the paper) along with a demonstration that ST's axioms are satisfied by the model provided in `CentralTheorems/modelsHTOT.lean`.

**Note**: Many of the theorems proved in the `proofs_###.lean` files are largely superfluous and/or footnote remarks, but they are not without purpose. For one, they serve as verifications that the timelines defined in each theory, say HT, RT, ST, and B, are indeed behaving as intended. Thus, the paper which this repository follows will use them in some of its prose and explanatory sections in order to further validate the selected definitions and axioms insofar as they properly encode the intended concepts. Secondly, several theorems may become unexpectedly useful in the construction of models for the primary proof (found in the file(s) `modelsHTOT.lean`, `modelsRT.lean`, or `modelsST.lean` under the folder *CentralTheorems*).

## Important Remark

Each proof and definition stated and verified within the *Verification* folder is intended for the guarantee of syntactic validity and derivability. No stated definition or theorem can, by itself, serve as irrefutable proof for the thesis made in the accompanying paper, that substantival and relational time theories can be generalized in such a way as to not be contradictory with one another. Such a conclusion only follows when the additional premises established in the paper are granted (namely, that the theories ST and RT truly do encode, at the very least, the great majority of relational and substantival time theories and that the definition of "moments," should such a definition ever be defined intensionally, would not be incompatible with HT + OT). These additional premises, once granted, still merely grant a relatively weak conclusion, which was stated in the accompanying paper: There exists at least one theory of time, even if not itself the "true" theory of time, in which both relational time and substantival time theories are satisfied.

## Notation Translation (Lean 4 to LaTeX)

|Notation            |Lean4               |
|--------------------|--------------------|
|$\mathbb H ^ n$     |`order_set n`       |
|                    |                    |
|                    |                    |
|                    |                    |
|                    |                    |
|                    |                    |
|                    |                    |

## Theorems Cited in Paper

| Theorem | Page #s |
|---------|---------|
|INV0     |Pg. 3    |
|INV7     |Pg. 4    |
|         |         |
|         |         |
|         |         |
|         |         |
|         |         |
|         |         |

## Requirements

This repository was developed and verified using **Lean 4.33.0-rc1**.

To check your installed Lean version, run:

```bash
lean --version
```

The proofs in this repository are intended to be checked using the Lean version specified by the project's toolchain configuration.

## Building and Verification

From the root directory of the repository, run:

```bash
lake build
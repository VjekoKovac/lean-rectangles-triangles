# Verification record

The four public results are the declarations in `Solution.lean`. The source, target names and versions for this release can be traced using the records below.

| Question | Check and evidence |
| --- | --- |
| Do all project modules compile? | [Build transcript](clean-build.txt). A separate working copy started with an empty project build directory and used the pinned dependency cache. The build resumed after an interruption and finished with exit status 0. Lake's job count includes dependencies. The four warnings in the Challenge come from its four specified goals. Individual proof modules also produce some linter or deprecation warnings. |
| Do the proofs solve the reviewed Challenge? | [Full Comparator transcript](comparator.txt). The log identifies the four names exported separately from Challenge and Solution, the kernel checks, and the exit status. The [host note](host/README.md) documents the Linux sandbox configuration. The Challenge is an independent, mathlib-only source file. |
| Which axioms support the results? | [All four reports](axioms.txt). The script compares the target names and checks each transitive axiom set. The solution proofs use precisely `propext`, `Classical.choice`, and `Quot.sound`. The imported [prime number theorem in arithmetic progressions](prime-number-theorem.txt) also has this axiom set. |
| Are any placeholders or native-execution proof shortcuts present in the project proof sources? | [Source check](source-check.txt). The only four proof placeholders are the four reference statements in the Challenge. The mechanical evidence for the trust boundary is the kernel and axiom checking above. |
| Which calculations were independently tested? | The [three-point lattice set](ordered-counts.txt), [circle over the field of three elements](prime-three.txt), and [two dyadic blocks](two-block.txt) are separate Lean proofs by kernel reduction. Their [Lean sources](../reviews) specify the values. [Configuration module replays](leanchecker-configuration.txt) and the [weight approximation check](weight-approximation.txt) record further component checks. |
| Which release and dependencies reproduce the checks? | [Tool versions and dependency commits](versions.txt) includes the bundled NanoDa executable digest, the Lean commit and all resolved dependency revisions. Run `sha256sum -c evidence/input-sha256.txt` at the repository root to compare all Lean sources and the four build and checking inputs to the [file digests](input-sha256.txt). |
| Who checked the mathematical meaning? | A separate AI reviewer compared the [statements](../reviews/statement-fidelity.md) with the paper, read the [proofs](../reviews/proof-correctness.md), and checked concrete examples. A further AI reviewer independently wrote and elaborated several expanded target types and checked the PNT hypotheses. The [cross-check report](../reviews/final-cross-check.md) contains its command and output. |
| What was tested for Palomar? | [Local metadata and source-format validation](metadata-check.txt) and [workflow checks](workflow-check.txt). The public repository, GitHub-hosted builds, official Palomar run, editorial review and registration await publication. Human mathematical sign-off has not been recorded. |

A separate [negative control](comparator-control.txt) checked the axiom policy. Its synthetic solution proved `True` by citing a fresh, unapproved axiom. Both synthetic modules built. Comparator rejected the solution, named the offending axiom, and returned exit status 1. Only the transcript of this control is included in the repository.

The local full replay checks Lean and NanoDa. Palomar's verifier also attempts con-ron on its own protected export. That registry-specific replay and resource profile have not been exercised here. [Pinned Palomar verification pipeline](https://github.com/PalomarRegistry/PalomarSubmission/tree/14aa8d6b3c2f14a8540605e37144560b9a00e7e7)

## Source identity

The four source statements use the printed numbering of Bennett, Kovač, Nakamura, and Oliveira, *Rectangles, triangles and Schrödinger waves*, arXiv:2606.30178v1. The [versioned paper](https://arxiv.org/abs/2606.30178v1) is the bibliographic source. The source comparisons use the introduction on printed pages 3, 8, and 9 and the relevant proof sections. These are the SHA-256 digests of the two inputs examined.

```text
a0b37ca6006ff2dcf0e75f4cd6cdcc6bfe0552f829a70ecce05d7703009a58e9  rectangles_triangles_main.tex (uploaded source)
818780744f7c2600d972764b65adf2ee925e4d36d5aa694a8986c18fe46df31a  2606.30178v1.pdf (arXiv PDF)
```

The [statement guide](../STATEMENTS.md) records the measure conventions. In particular, the essential closed support is used for Euclidean L² data, and nonnegative lower integrals specify the values of X-rays on exceptional individual lines. The [proof guides](../blueprints) identify the estimates that suffice for each introductory theorem and the points where the implementation changes the paper’s proof.

# Rectangles, triangles and Schrödinger waves

Lean 4 proofs of all four theorems in the introduction of *Rectangles, triangles and Schrödinger waves*, by Jonathan Bennett, Vjekoslav Kovač, Shohei Nakamura, and Itamar Oliveira. The formalization authors are the same four authors. The original mathematical source is the first arXiv version, dated 29 June 2026. Item 1.1 is a question. [Paper on arXiv](https://arxiv.org/abs/2606.30178v1) · [Versioned PDF](https://arxiv.org/pdf/2606.30178v1)

## The four theorems

For the statements in conventional notation, including all the domains, normalizations and quantifiers, read [the statement guide](STATEMENTS.md). For the commands, their output and the scope of each check, read [the verification record](evidence/README.md).

Here $N$ is a **real** frequency or box radius and $n$ is an **exact** support cardinality. In the table, MT means Mizohata–Takeuchi. Each proof guide specifies the definitions, hypotheses, proof steps, and corresponding Lean declarations.

| Paper | Public Lean declaration | Assertion | Proof guide |
| --- | --- | --- | --- |
| 1.2, p. 3 | `RTS.combinatorial_growth` | For one absolute $c>0$, the unpinned extremum dominates the pinned extremum, which is at least $(\log x)^{c/\log\log\log x}$ both for every sufficiently large radius $x=N$ and for every sufficiently large cardinality $x=n$. | [Finite fields, lattice lifting, and interpolation](blueprints/01-combinatorics.md) |
| 1.3, p. 8 | `RTS.quantitative_transference` | For every $d\ge1$ and $N\ge1$, each periodic constant at $N$, Stein or MT, is at most its Euclidean counterpart at $N+1$, with coefficient one. | [Transference and packet limits](blueprints/02-transference.md) |
| 1.4, p. 8 | `RTS.configuration_lower_bounds` | In dimension two, for every $N\ge1$ and $n\ge1$, the box and cardinality Stein constants dominate the respective unpinned configuration ratios. Both MT constants dominate the corresponding pinned ratios. All four comparisons have coefficient one. | [The fourth moment and ray counts](blueprints/03-configuration.md) |
| 1.5, p. 9 | `RTS.trigonometric_growth` | In every dimension $d\ge1$, both periodic constants are at least $c_d(\log N)^d$ for all sufficiently large $N$. At every sufficiently large $n$, each cardinality constant lies between $c'_d n$ and $C_d n$. The three multiplicative constants are positive and finite. | [Dyadic frequencies and exact support sizes](blueprints/04-weights.md) |

[Challenge.lean](Challenge.lean) contains the mathematical definitions and the four reference statements, with only mathlib imports. Its four `by sorry` placeholders mark the propositions posed to the independent solution. [Solution.lean](Solution.lean) gives four proved declarations with the same names in a separate import tree. The [axiom report](evidence/axioms.txt) lists exactly `propext`, `Classical.choice`, and `Quot.sound` for each solution theorem. The [Comparator configuration](comparator.json) selects all four together. **Both NanoDa and the Lean kernel accepted the solution.** Comparator exited with status 0. The [comparison transcript](evidence/comparator.txt) records the complete command and output.

## Open the project in VS Code

1. Install Git, Visual Studio Code, and the official **Lean 4** extension. Follow the extension’s setup guide to install the Lean toolchain manager. Python 3 is also used by the repository’s verification scripts. [Official Lean installation guide](https://lean-lang.org/install/)
2. Extract the ZIP. In VS Code choose **File → Open Folder** and select the folder where `lean-toolchain`, `lakefile.toml`, `Challenge.lean`, and `Solution.lean` are visible side by side.
3. Choose **Terminal → New Terminal**. Run the following commands, one at a time. Lake picks the pinned Lean release from the current directory. The first build downloads dependencies and may take considerable time, particularly for the prime-number-theorem dependency.

```sh
lake exe cache get
lake build
lake env lean AxiomReport.lean
```

4. Begin with Theorem 1.4. In [Challenge.lean](Challenge.lean), find `ConfigurationLowerBounds`. Its four lines joined by `∧` are the four inequalities on page 8. Read `perStein`, `perMT`, `boxRatio`, and `pinnedBoxRatio` with **Go to Definition** (F12). On a Lean identifier, hovering displays its type.
5. Open [Solution.lean](Solution.lean) and follow `Configuration.configurationLowerBounds` with F12. In [the proof module](RTS/ConfigurationProof.lean), click a tactic to see hypotheses and the goal in **Lean Infoview**. To see the effect of a single tactic, move the cursor from its beginning to its end. For a small numerical example, open [the three-point test](reviews/OrderedCounts.lean). It checks 15 ordered rectangles, 11 ordered isosceles triangles, and pinned counts 5, 3, and 3.

## Reproduce the checks

The build uses Lean **4.35.0** and mathlib **v4.35.0**. Keep `lean-toolchain` and `lake-manifest.json` under version control. The manifest fixes mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679` and PrimeNumberTheoremAnd at `a4fb6989b07e9c76b511807ae93e33e25b820e9b`. The latter supplies a kernel-checked prime number theorem in arithmetic progressions for the solution to Theorem 1.2. [Pinned manifest](lake-manifest.json) · [Proof of the prime-product bound](RTS/PrimeProducts.lean)

After `lake build`, run these commands in the project folder. On Windows, use `py -3` if that is how your installation exposes Python.

```sh
python3 scripts/check-source.py
python3 scripts/check-axioms.py
lake env lean -DwarningAsError=true reviews/OrderedCounts.lean
lake env lean -DwarningAsError=true reviews/PrimeThree.lean
lake env lean -DwarningAsError=true reviews/TwoBlock.lean
```

The first script checks the file layout, the four target names, and the absence of several forbidden proof constructs in the project proofs. The second runs Lean’s `#print axioms` for the four theorem declarations and checks each transitive axiom set. The final three commands replay finite mathematical tests. The build also checks the symbolic inequalities, using tactics such as `norm_num`, `omega`, and `ring` that generate Lean proof terms.

On Linux with Bash, Python 3, bubblewrap, and usable user namespaces, run the independent statement comparison from the project root. The script uses the installed Lean release’s Comparator and bundled NanoDa binary. [How the recorded verification host was configured](evidence/host/README.md)

```sh
bash scripts/compare.sh comparator.json
```

## Sources, proof choices, and review

- Theorem 1.2 reuses `chebyshev_asymptotic_pnt` from the PrimeNumberTheoremAnd project to select primes congruent to three modulo four. Mathlib supplies the Chinese remainder equivalence `ZMod.prodEquivPi` and the quadratic nonresidue lemma `ZMod.mod_four_ne_three_of_sq_eq_neg_one`. The lift retains enough primitive directions to prove the lower rectangle count and upper pinned-triangle count used in the conclusion. The first guide distinguishes these estimates from the paper’s more precise auxiliary asymptotic formulas. [PrimeNumberTheoremAnd source](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/a4fb6989b07e9c76b511807ae93e33e25b820e9b) · [Mathlib source](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679)
- Theorem 1.3 uses translated rectangular packets in frequency space and mathlib’s torus Parseval theorem, `UnitAddTorus.hasSum_sq_mFourierCoeff`, formalized by David Loeffler. The guide explains how the common packet mass cancels, retaining the sharp transfer coefficient. Theorem 1.5 uses the same dyadic construction as the paper and directly injects marked choices into the resulting collision count. [Packet identity](RTS/PacketIdentities.lean) · [Dyadic multiplicity proof](RTS/WeightMultiplicity.lean)
- Codex generated the proof files. Separate AI reviews compared the source to the challenge and inspected the proof and its readability. The statement review discusses the choice of a lower integral on exceptional line restrictions of measurable weights. A human coauthor’s sign-off and Palomar’s editorial review are separate from the recorded machine checks. [Statement fidelity](reviews/statement-fidelity.md) · [Proof correctness and clarity](reviews/proof-correctness.md)

## Publish from VS Code and submit to Palomar

1. With the **extracted project folder** open, choose **Source Control → Initialize Repository** in VS Code. Stage the project files, enter a first commit message, and select **Commit**. The included `.gitignore` excludes the local Lean build cache.
2. Choose **Publish to GitHub**, sign in, and select **Publish to GitHub public repository**. A suggested repository name is `lean-rectangles-triangles`. On the GitHub repository’s **Code** tab, check that `Challenge.lean`, `Solution.lean`, `formalization.yaml`, and `.github/` appear at the top level. Publishing the first commit queues **Actions → Lean build** automatically. Each later push to any branch, including a change to `formalization.yaml` alone, queues another build. After a local commit, choose **Push** or **Sync Changes** in VS Code. A commit made in GitHub’s web editor reaches the branch immediately. Open the run for your commit and select **Build and verify Lean proofs** to follow `lake build`.
3. To try the Palomar verifier on GitHub before submitting, choose **Actions → Palomar preflight → Run workflow**, select the revision, and choose your relationship to the formalization. Use the default `full` mode to run the public pipeline’s proof checks. The lighter `preflight` mode checks the submission inputs only. The report is available as a workflow artifact. [Manual workflow](.github/workflows/palomar-preflight.yml)
4. Review the authors, proposed Apache-2.0 license, responsible maintainer, and public description. If you edit a file, commit and push it. Then run `git rev-parse HEAD` in VS Code’s terminal. Copy the **full 40-character SHA**. GitHub also offers **Copy full SHA** beside the commit in the commits list. [Project metadata](formalization.yaml) · [License](LICENSE)
5. On the Palomar submission form, enter your **public repository URL** and that **full commit SHA**. The project directory is the repository root, the Comparator path is `comparator.json`, and the metadata path is `formalization.yaml`. These are the default locations. The single configuration selects all four theorems for one entry. Select the relationship to the formalization that applies to you and keep the returned status URL. GitHub publication, hosted verification, and registration are performed against the public commit. [Palomar instructions](https://palomar-registry.org/how-to-submit) · [Submission form](https://submit.palomar-registry.org)
6. Follow that status page through mechanical and editorial review. Once registration is available, use the page to register the reviewed result. A later source or metadata change produces a different commit and requires its own review. [Example GitHub project](https://github.com/roos-j/lean-dfr) · [Example Palomar entry](https://palomar-registry.org/entry?id=PALOMAR-2026-10-21-000004&version=1)

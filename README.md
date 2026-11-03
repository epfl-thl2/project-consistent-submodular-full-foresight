# Consistent submodular maximization with full foresight

Lean proofs of the results of *Consistent Submodular Maximization with Full
Foresight*: for clairvoyant algorithms that maintain a solution of at most `k`
arrived elements with constantly many changes per arrival, the optimal
approximation ratio is `ξ⋆ ≈ 0.7942` for randomized algorithms and `3/4` for
deterministic ones (Main Results 1 and 2). Every numbered theorem, lemma, and
proposition of the paper is stated and proved.

## Statements

[MainStatements.lean](ConsistentSubmodular/MainStatements.lean) imports only Mathlib.
It contains the model, the definitions the statements use, and one statement
per result of the paper, in the paper's order. It is the only file a reader
has to check to know what is proved.
[MainResults.lean](ConsistentSubmodular/MainResults.lean) exports one theorem per
statement, with exactly the stated type:

| Paper | Statement | Theorem |
| --- | --- | --- |
| Main Result 1 (tight randomized bound) | `RandomizedTightGoal` | `randomizedTight` |
| Main Result 2 (tight deterministic bound) | `DeterministicTightGoal` | `deterministicTight` |
| Theorem 1 (randomized impossibility, `ξ⋆ + O(ε)`) | `RandomizedUpperGoal` | `randomizedUpper` |
| Remark 1 (randomized impossibility, constant recourse) | `RandomizedUpperLimitGoal` | `randomizedUpperLimit` |
| Theorem 2 (randomized algorithm) | `RandomizedLowerGoal` | `randomizedLower` |
| Lemma 1 (addition robustness to consistency) | `AdditionRobustReductionGoal` | `additionRobustReduction` |
| Lemma 2 (interval selection to addition robustness) | `IntervalSelectionReductionGoal` | `intervalSelectionReduction` |
| Lemma 3 (reduction to consecutive intervals) | `ConsecutiveIntervalReductionGoal` | `consecutiveIntervalReduction` |
| Lemma 4 (consecutive intervals) | `ConsecutiveIntervalGapGoal` | `consecutiveIntervalGap` |
| Proposition 1 (the root `ξ⋆` of `Ψ`) | `PsiRootGoal` | `psiRoot` |
| Lemma 5 (finite minimax duality) | `MinimaxGoal` | `minimax` |
| Theorem 3 (deterministic impossibility, `3/4 + O(ε)`) | `DeterministicUpperGoal` | `deterministicUpper` |
| Main Result 2, impossibility for constant recourse | `DeterministicUpperLimitGoal` | `deterministicUpperLimit` |
| Theorem 4 (deterministic guarantee) | `DeterministicLowerGoal` | `deterministicLower` |
| Theorem 5 (reduction to clairvoyant certificates) | `CertificateReductionGoal` | `certificateReduction` |
| Theorem 6 (certificates at `1/√2`) | `SqrtTwoCertificatesGoal` | `sqrtTwoCertificates` |
| Theorem 7 (certificates at `3/4`) | `ThreeQuarterCertificatesGoal` | `threeQuarterCertificates` |
| Lemma 6 (behavior on the stream `Σ`) | `GridStreamCrossingGoal` | `gridStreamCrossing` |
| Lemma B.1 (window bounds) | `WindowBoundsGoal` | `windowBounds` |
| Lemma B.2 (mixture comparisons) | `MixtureComparisonsGoal` | `mixtureComparisons` |
| Lemma B.3 (two-type interpolation) | `TwoTypeInterpolationGoal` | `twoTypeInterpolation` |
| Theorem B.4 (prefix–suffix tradeoff) | `PrefixSuffixTradeoffGoal` | `prefixSuffixTradeoff` |
| Lemma B.5 (prefix bound) | `PrefixBoundGoal` | `prefixBound` |
| Lemma B.6 (suffix bound) | `SuffixBoundGoal` | `suffixBound` |
| Lemma B.7 (concentration) | `ConcentrationGoal` | `concentration` |

Definitions 2.1, 2.2, 2.3, and 3.1 are `WindowInstance.IsAdditionRobust`,
`IntervalInstance.adaptivityGap`, `IntervalInstance.IsNonincreasingConsecutive`
with `IntervalInstance.IsEqualizing`, and `WindowInstance.Certificate`.
Remark 2 comments on Lemma 6 and makes no claim of its own.

Use the results with Lean's module system:

```lean
module
import ConsistentSubmodular

example : ConsistentSubmodular.RandomizedTightGoal := ConsistentSubmodular.randomizedTight
example : ConsistentSubmodular.DeterministicTightGoal := ConsistentSubmodular.deterministicTight
```

## From the paper to Lean

- **Streams and algorithms.** The stream consists of the elements
  `0, ..., n - 1` in arrival order, and a trajectory chooses a set at every time
  `0, ..., n`. A trajectory may depend on the entire stream, so it describes a
  clairvoyant algorithm, but it may select only arrived elements.
  `FeasibleTrajectory k C` adds the cardinality bound `k` and the consistency
  bound `C` on the symmetric difference at every update. A randomized
  clairvoyant algorithm is described by the law of its trajectory,
  `RandomTrajectory`: a probability distribution on the finitely many
  trajectories, every one of which must be feasible.
- **Objectives** are nonnegative, monotone, and submodular; their value at the
  empty set may be nonzero.
- **Constants.** Every `O(·)` of the paper is an explicit constant `K` chosen
  before the remaining parameters. In particular, the recourse bounds are
  chosen before the stream length, the budget, and the objective.
- **Window instances.** `WindowInstance` is the clairvoyant addition-robust
  instance of Section 2.3 together with the candidates `O_0, ..., O_m`;
  Section 3.2 calls the same data a window instance. Prefixes of the future are
  nested sets, so a stage may add several elements, as in Appendix B.2.1;
  `SingleArrivals` is the case of one arrival per stage. Lemma 1 and Theorem 5
  assume their hypotheses only for single arrivals.
- **Mixtures.** `mixtureValue` is `H_j(p)` of equation (3), the exact finite
  expectation over the random set of candidates. `bufferMixtureValue`,
  `physicalVector`, and `multilinearExtension` are `H_Q(p)`, `z(p)`, and
  `F_Q(z)` of Appendix B.2.1, and `independentExpectation` is the expectation
  over a random set whose elements are included independently.
- **The linear program (1).** `lpValue` is its value `ρ⋆`, and `payoff` is the
  normalized payoff `w_{i,j}` of Lemma 5.
- **The constant `ξ⋆`** is defined as the root of `Ψ` in `(1/2, 1)`;
  Proposition 1 shows that it exists and is unique.

## Proof structure

[MainResults.lean](ConsistentSubmodular/MainResults.lean) assembles each result
from the results it depends on in the paper; for instance, Theorem 2 chains
Lemmas 4, 3, 2, and 1 as in Appendix A.7. The supporting modules mirror the two
halves of the paper:

```text
ConsistentSubmodular/
├── MainStatements.lean        the model and every statement (imports only Mathlib)
├── MainResults.lean           one theorem per statement
├── Randomized/                Section 2 and Appendix A
│   ├── Constants.lean         Proposition 1; the constants u₁, q, ξ⋆
│   ├── AdaptivityGap/         Lemmas 2–5
│   ├── Reduction/             Lemma 1 (Algorithm 1) and Theorem 2
│   └── Impossibility/         Theorem 1 and Remark 1
└── Deterministic/             Section 3 and Appendix B
    ├── Basic/                 shared facts, and Lemmas B.1–B.3 (Appendix B.2.1)
    ├── Certificates/          Theorems 6 and 7, Theorem B.4, Lemmas B.5 and B.6
    ├── Reduction/             Theorem 5 and Lemma B.7 (Appendices B.2.3 and B.2.4)
    └── Impossibility/         Theorem 3 and Lemma 6 (Appendix B.1)
```

Theorem 4 is assembled in `MainResults.lean` from Theorems 5 and 7.

Within the randomized part:

| Result | Modules |
| --- | --- |
| Proposition 1; `u₁`, `q`, and `ξ⋆ = 1/(1 + u₁u₂)` | `Constants` |
| Lemma 4: the chain inequalities (14)–(16) and the equality case (17) | `ConsecutiveChains`, `ConsecutiveIntervals` |
| Definition 2.3: the equalizing distribution (5) of nonincreasing consecutive intervals | `EqualizingDistribution` |
| Lemma 3: shadow intervals (6), the step functions `W`, `H`, `X`, `g`, identities (10) and (11), averaging over chains | `ShadowIntervals`, `StepIntegrals`, `ShadowChains`, `ConsecutiveReduction` |
| Lemma 5 | `Minimax` |
| Lemma 2 | `IntervalSelection` |
| Lemma 1 and Theorem 2 | `CheckpointLaw`, `CheckpointSchedule`, `CheckpointWindow`, `CheckpointAlgorithm`, `Checkpoints` |
| Theorem 1 and Remark 1 | `HardStream`, `HardScalar`, `HardInstance` |

Within the deterministic part:

- **Theorem 3 and Lemma 6** (Appendix B.1) are proved on the stream `Σ` in
  [GridStream.lean](ConsistentSubmodular/Deterministic/Impossibility/GridStream.lean),
  with the coverage counts in
  [GridStreamCoverage.lean](ConsistentSubmodular/Deterministic/Impossibility/GridStreamCoverage.lean).
- **Theorem 5** is proved in
  [CertificateReduction.lean](ConsistentSubmodular/Deterministic/Reduction/CertificateReduction.lean)
  at accuracy `N = ⌊20/ε⌋ + 200`. Each window of the protected clock is
  compressed to `3N + 2` retained stages
  ([FractionalWindow.lean](ConsistentSubmodular/Deterministic/Reduction/FractionalWindow.lean)),
  and a certificate of the compressed window is rounded with shared thresholds.
  A compressed stage may add several arrivals; its certificate comes from the
  single-arrival encoding in
  [ArrivalEncoding.lean](ConsistentSubmodular/Deterministic/Reduction/ArrivalEncoding.lean).
  The module's documentation lists the modules behind each step of
  Appendices B.2.3 and B.2.4. The concentration bounds of Lemma B.7 are in
  [ExponentialTails.lean](ConsistentSubmodular/Deterministic/Reduction/ExponentialTails.lean).
- **Lemmas B.1–B.3** (Appendix B.2.1) are proved in
  [WindowBounds.lean](ConsistentSubmodular/Deterministic/Basic/WindowBounds.lean).
- **Theorem 6, Theorem B.4, and Lemmas B.5 and B.6** (Appendix B.2.2) are
  proved in
  [HalfMixtureCertificate.lean](ConsistentSubmodular/Deterministic/Certificates/HalfMixtureCertificate.lean).
- **Theorem 7** is proved in
  [WindowCertificates.lean](ConsistentSubmodular/Deterministic/Certificates/WindowCertificates.lean)
  by applying the finite checkpoint theorem for atomic profiles
  ([AtomicProfiles.lean](ConsistentSubmodular/Deterministic/Certificates/AtomicProfiles.lean),
  [FiniteCheckpoint.lean](ConsistentSubmodular/Deterministic/Certificates/FiniteCheckpoint.lean))
  to the compatible type profile of the window. A natural-language account of
  this proof is provided in
  [docs/three_quarter_certificate.pdf](docs/three_quarter_certificate.pdf).

The reduction of Theorem 5 uses only the shared modules in `Basic/`, not the
certificate constructions: as in the paper, it assumes certificates and does
not depend on how they are built.

## Verify the proofs

Install Git, [elan](https://github.com/leanprover/elan), and Python 3.10 or newer,
then run:

```sh
git clone https://github.com/epfl-thl2/project-consistent-submodular-full-foresight.git
cd project-consistent-submodular-full-foresight
lake exe cache get
python3 scripts/verify.py
```

The script builds the project with warnings treated as errors, checks every
exported theorem against its statement, and audits their axioms with
[MainAxioms.lean](validation/MainAxioms.lean). It also checks that supporting
results are absent from the public module interface. Fresh logs and a receipt
with source hashes are saved under `validation/local_runs/` and are not
committed. All exported theorems use only Lean's standard axioms `propext`,
`Classical.choice`, and `Quot.sound`; the verification rejects any other axiom,
including `sorryAx` from an admitted proof.

### Comparator

[Comparator](https://github.com/leanprover/comparator) is the Lean FRO's judge
for formal proofs. [comparator/Challenge.lean](comparator/Challenge.lean)
states every theorem with its proof left open, and
[comparator/Solution.lean](comparator/Solution.lean) imports the proofs. Run

```sh
python3 scripts/verify.py --comparator   # or: python3 scripts/comparator.py
```

to check, for every theorem in [comparator/config.json](comparator/config.json),
that the solution proves exactly the challenge's statement (including every
definition it depends on), uses only the three standard axioms, and is accepted
by the Lean kernel when replayed from an export of all its declarations. The
script builds the pinned tools for this Lean version under
`.lake/comparator-tools/` on first use: lean4export at tag `v4.30.0-rc1` and
comparator at its last commit for Lean `v4.30.0-rc1` (comparator later moved
into Lean core as `lake comparator`). Comparator sandboxes the builds with
[landrun](https://github.com/Zouuup/landrun), which needs Linux. Where landrun
is missing, as on macOS, the script substitutes a pass-through shim and says
so; the checks are unchanged, but the builds are not sandboxed.

The build is pinned to Lean `4.30.0-rc1` and mathlib commit
`0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`; transitive dependencies are pinned
in [lake-manifest.json](lake-manifest.json). All definitions, proofs, and build
inputs are included; no other local checkout is required.

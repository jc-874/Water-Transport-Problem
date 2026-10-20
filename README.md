# Water Transport in Lean

Lean 4 formalizations of three papers on averaging water levels on finite
graphs. The three libraries share the definitions of a state, a legal averaging
operation, a finite strategy, reachability, and optimality.

## Papers and proof status

| Library | Paper / topic | Formalized results |
| --- | --- | --- |
| [`WaterTransport1`](WaterTransport1) | *Water Transport on a Path: Finding the Strategy Through Its Existence* | Convergence and finite reachability of limits, attainment of continuous objectives, the path two-step theorem, the star algorithm, and the three examples. |
| [`WaterTransport2`](WaterTransport2) | *3-spider 上的 water transport problem 所需策略是任意长的* (arbitrarily long optimal strategies on 3-spiders) | Barrier inequalities and equality cases, lexicographic extremality, explicit separating weights, and unbounded optimal strategy length as the graph size grows. |
| [`WaterTransport3`](WaterTransport3) | *A Uniform Bound on Optimal Strategy Length in Water Transport Problem* | Local operator geometry, uniform convex-hull stabilization, explicit and asymptotic length bounds, and correctness of exact search for rational inputs. |

**Papers 1 and 2 have no `sorry` dependencies. Paper 3 is partially complete.**
Its main uniform-bound and exact-search results do not depend on `sorry`.
Section 6 still has three deferred certificate bounds, listed below.
The bit-complexity analysis, binary encoding, and NEXP membership claim are
not formalized.

The path theorem in Paper 1 is proved using general attainment and a shortest
globally optimal strategy. The finite-horizon stabilization statement follows
from that theorem. This implementation does not provide a separate proof
avoiding the Axiom of Choice.

## Requirements and build

Install [Lean through elan](https://lean-lang.org/install/).
The repository pins:

- Lean: `leanprover/lean4:v4.32.0`.
- mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.

Clone this repository:

```sh
git clone https://github.com/jc-874/Water-Transport-Problem.git
cd Water-Transport-Problem
```

Open the repository root in VS Code with the Lean 4 extension. From that same
directory, run:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean AuditProgress.lean
```

`lake-manifest.json` records the dependency revisions. No sibling project or
machine-specific path is needed. The `.lake` directory contains downloaded
dependencies and build artifacts and is not part of the repository.

The exact finite certificates in Paper 1 can take several minutes to check on
a first build. A successful build alone does not establish the absence of
`sorry`: run both audits to check the declared proof status.

To build one paper, use `lake build WaterTransport1`,
`lake build WaterTransport2`, or `lake build WaterTransport3`. Later papers
automatically build their dependencies from Paper 1.

## Import entry points

```lean
import WaterTransport   -- all three papers
```

Alternatively, import `WaterTransport1`, `WaterTransport2`, or `WaterTransport3`.
The four short root files contain imports rather than new mathematical
declarations; they are the entry points used by Lake and the audits.

The mathematical namespaces are `WaterTransport` for Paper 1,
`WaterTransport.Paper2` for Paper 2, and `WaterTransport.Paper3` for Paper 3.

## Reading order and core results

File numbers give a reading order compatible with imports; they are not the
section numbers of the papers. Later papers reuse the first paper's model.

| Modules | Purpose |
| --- | --- |
| `WaterTransport1/S01`–`S02` | States, connected-set averaging, strategies, optimality, reverse profiles, and exact rational execution. |
| `WaterTransport1/S03`–`S05` | Analysis, attainment of optimal values, and the shortest optimal length. |
| `WaterTransport1/S06`–`S08` | Path geometry, shortening, and the public path theorems. |
| `WaterTransport1/S09` | The star algorithm and its optimality. |
| `WaterTransport1/S10`–`S11` | Finite certificate checkers, their soundness, and the three examples. |
| `WaterTransport2/S01`–`S04` | The spider construction, barriers, lexicographic comparisons, and the length lower bound. |
| `WaterTransport3/S01`–`S03` | Operators, local geometry, and the uniform bound. |
| `WaterTransport3/S04` | The five-vertex repetition example, including the explicitly deferred certificates. |
| `WaterTransport3/S05` | Exact search for rational input and its correctness. |

Key public declarations, relative to each paper's namespace:

| Paper | Declaration | Meaning |
| --- | --- | --- |
| 1 | `continuous_objective_attained` | A continuous objective on nonnegative states attains its supremum at a finitely reachable state. |
| 1 | `path_optimalLength_le_two` | At most two moves suffice on a path. |
| 1 | `endpoint_optimalLength_le_one` | At most one move suffices at a path endpoint. |
| 1 | `starGreedyStrategy_optimal`, `star_optimalLength_le` | The stated leaf-order algorithm is globally optimal; at most one move per leaf suffices. |
| 2 | `optimalLength_lower_bound`, `no_uniform_bound` | The constructed 3-spider instances require arbitrarily many moves. |
| 3 | `uniform_convex_stabilization` | The convex hull of all strategy operators equals that of operators within the explicit finite horizon. |
| 3 | `uniformLength_le_explicitBound`, `uniformLength_asymptotic` | Explicit and asymptotic estimates for the uniform horizon. |
| 3 | `exactSearch_correct` | The finite rational search returns a globally optimal strategy within that horizon. |

## Model conventions

- Graphs are finite simple graphs. A legal move averages a nonempty set whose
  induced subgraph is connected.
- `State V` means `V → ℝ`; physical nonnegativity is the explicit predicate
  `Nonnegative`.
- `run [S, T] w` applies `S` first and `T` second. The empty list is a legal
  zero-step strategy.
- `Reachable G w u` requires exact reachability by a finite legal strategy,
  not membership in a closure.
- `IsOptimal` compares against all finite legal strategies. `horizonMax`
  compares only against strategies within a specified length bound.
- `RepetitionFree` forbids repeating any set containing at least two vertices;
  singleton identity moves are ignored.
- `energy` is the sum of squared coordinates. It is not the ambient norm.
- Operator convex hulls use finite convex combinations, without adding a
  closure operation.

## Deferred Section 6 certificates

In [`WaterTransport3/S04_RepetitionExample.lean`](WaterTransport3/S04_RepetitionExample.lean),
the following declarations in `WaterTransport.Paper3.RepetitionExample`
contain explicit `sorry` proofs:

- `arbitrary_strategy_bound`
- `repetitionFree_bound`
- `three_step_bound`

The supplementary certificates needed for these bounds have not been supplied.
Four further declarations depend on them and are also pending:
`witness_optimal`, `targetSup_value`, `every_optimal_repeats`, and
`shortest_length`. These seven declarations must not be cited as verified
results.

The graph, input weights, legality of the concrete witnesses, their evaluated
target values, and the decrease after the first move are proved independently.
The main results in `S03_UniformBound` and `S05_ExactSearch` are independent of
the deferred certificates.

## Audits

[`Audit.lean`](Audit.lean) checks every declaration from Paper 1, including
private helpers, for transitive axiom dependencies. Only `propext`,
`Classical.choice`, and `Quot.sound` are accepted. It also checks the preserved
statements and definitions and several model boundary cases.

[`AuditProgress.lean`](AuditProgress.lean) checks Papers 2 and 3. It permits
`sorryAx` only for the seven explicitly named pending declarations above;
any other declaration depending on `sorryAx` causes the audit to fail.

The fixed baselines in [`Research`](Research) are inputs to the declaration
checks. They preserve 223 declarations from Paper 1 and 140 from Papers 2 and 3.
Do not regenerate the baselines to make an altered mathematical statement pass.

Finite numerical certificates use exact arithmetic and Lean kernel checks.
There are no project-specific axioms asserting the results of an external
program.

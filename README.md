# Water Transport in Lean

This project formalizes three papers about maximizing water levels by complete
averaging on connected vertex sets. The mathematical definitions and main
results are stated below in the papers' notation, followed by their Lean
declarations and the build instructions.

| Main file | Paper / topic |
| --- | --- |
| [`WaterTransport1.lean`](WaterTransport1.lean) | *Water Transport on a Path: Finding the Strategy Through Its Existence* |
| [`WaterTransport2.lean`](WaterTransport2.lean) | Arbitrarily long shortest optimal strategies on 3-spiders |
| [`WaterTransport3.lean`](WaterTransport3.lean) | *A Uniform Bound on Optimal Strategy Length in Water Transport Problem* |

All 15 main declarations listed in the correspondence table below are proved
without `sorry` dependencies. The formalization of Paper 3 as a whole is
partial: its repetition example remains pending, and its algorithmic
complexity claims are outside the current scope.

## 1. Common mathematical model

Let $G=(V,E)$ be a **finite undirected simple graph**. An initial water-level
vector is a function $w:V\to\mathbb R_{\ge 0}$. The graph need not be connected.
For the linear-algebraic discussion, the same averaging maps act on
$\mathbb R^V$.

A **legal move** selects a nonempty set $S\subseteq V$ such that the induced
subgraph $G[S]$ is connected. Its complete averaging operator is

$$
(A_Sw)(v)=
\begin{cases}
\displaystyle\frac{1}{|S|}\sum_{u\in S}w(u), & v\in S,\\
w(v), & v\notin S.
\end{cases}
$$

A **strategy** is a finite chronological sequence
$\sigma=(S_1,\ldots,S_k)$ of legal moves. Write

$$
|\sigma|=k,\qquad
A_\sigma=A_{S_k}\cdots A_{S_1}.
$$

The empty strategy has length zero and operator $I$. Moves may repeat;
singleton moves are identities. All optimizations below range over finite
legal strategies unless a length bound is explicitly imposed.

Following Paper 1, write $w\triangleleft u$ when $u=A_\sigma w$ for some
finite legal strategy. This is exact finite reachability. For a continuous
function $f:\mathbb R_{\ge0}^V\to\mathbb R$, define

$$
f_{\sup}(w)=\sup_{\sigma} f(A_\sigma w).
$$

Continuity is with respect to the usual finite-dimensional topology on the
nonnegative cone. In particular, for a target vertex $x\in V$, put

$$
w^*(G,x,w)=\sup_{\sigma}(A_\sigma w)(x).
$$

A strategy is **globally optimal at $x$** if its final target value equals
$w^*(G,x,w)$. The **shortest optimal length** is

$$
t(G,x,w)=
\min\bigl\{|\sigma|:(A_\sigma w)(x)=w^*(G,x,w)\bigr\}.
$$

Paper 1 proves that this minimum exists for every nonnegative initial vector
on a finite graph. Thus $t(G,x,w)$ is a nonnegative integer; the $+\infty$
case allowed in Paper 3's initial convention never occurs in this setting.

For later use, write
$\langle p,w\rangle=\sum_{v\in V}p(v)w(v)$ and let $e_x$ be unit mass at $x$.
Since each $A_S$ is symmetric, the **reverse profile** of $\sigma$ at $x$ is

$$
p_{\sigma,x}=A_{\sigma^{\mathrm{rev}}}e_x=A_\sigma^{\mathsf T}e_x,
\qquad
(A_\sigma w)(x)=\langle p_{\sigma,x},w\rangle.
$$

Each such profile is nonnegative and has total mass one. The shared model
also uses the energy $E(w)=\sum_{v\in V}w(v)^2$, the squared Euclidean norm.

## 2. Paper 1: finite attainment, paths, and stars

### Theorem 2.1 and Corollary 2.1: finite attainment

For every finite graph $G$, every $w:V\to\mathbb R_{\ge0}$, and every
continuous $f:\mathbb R_{\ge0}^V\to\mathbb R$, there exists a state $u$ such that

$$
w\triangleleft u
\qquad\text{and}\qquad
f(u)=f_{\sup}(w).
$$

In particular, taking $f(u)=u(x)$ proves that a finite legal strategy attains
$w^*(G,x,w)$ for every target vertex $x$.

### Theorem 3.1: at most two moves on a path

Let $P_n=\langle v_1,\ldots,v_n\rangle$ be the path on $n$ vertices. For every
nonnegative initial vector $w$ and every $x\in V(P_n)$,

$$
t(P_n,x,w)\le 2.
$$

The supporting modules also prove Lemma 3.1: if $x$ is an endpoint, then
$t(P_n,x,w)\le1$. For an arbitrary target, the maximum over strategies of
length at most two already equals the unrestricted supremum.

### Theorem 4.1: the center of a star

Let $K_{1,n}$ have center $o$ and $n$ leaves, so it has $n+1$ vertices. Then
for every nonnegative initial vector,

$$
t(K_{1,n},o,w)\le n.
$$

The explicit optimal strategy described in the paper is also proved correct:
list precisely the leaves whose **initial** water levels exceed $w(o)$, in
nondecreasing order of their initial levels, and average each listed leaf
with $o$ in turn. Equal initial levels may be ordered arbitrarily. If no
leaf exceeds the initial center level, the empty strategy is optimal.

The supporting modules additionally prove convergence and finite reachability
of limits for successive averaging sequences, continuity of $f_{\sup}$, and
Examples 4.1 and 4.2. Example 4.3 is intentionally excluded.

## 3. Paper 2: unbounded shortest optimal lengths on 3-spiders

### The graph and the reference profile

Fix an integer $m\ge2$. Let $G_m=S(m,1,1)$ have vertices

$$
V(G_m)=\{a_0,a_1,\ldots,a_m,b,c\},\qquad o=a_0,
$$

and edges $a_i a_{i+1}$ for $0\le i<m$, together with $ob$ and $oc$.
Thus $G_m$ is a tree with $m+3$ vertices and maximum degree three.
For $0\le j\le m$, set

$$
P_j=\{a_0,\ldots,a_j\}.
$$

Starting from $e_o$, perform the following moves in chronological order:

1. $P_m$;
2. $P_{m-1}\cup\{b\}$;
3. $P_{m-1}\cup\{c\}$;
4. For $j=m-2,m-3,\ldots,0$, average $P_j\cup\{b\}$ when $m-j$ is even,
   and $P_j\cup\{c\}$ when $m-j$ is odd.

Denote this strategy by $\sigma_m^{\mathrm{ref}}$ and its resulting
**reference profile** by

$$
p_m=A_{\sigma_m^{\mathrm{ref}}}e_o.
$$

The strategy $\sigma_m^{\mathrm{ref}}$ has exactly $m+2$ moves.

### Reachable profiles and the alternating lexicographic order

For $k\ge0$, define

$$
\mathcal R_k=\{A_\sigma e_o:|\sigma|\le k\},
\qquad
\mathcal R_{\mathrm{fin}}=\bigcup_{k\ge0}\mathcal R_k.
$$

For $q\in\mathcal R_{\mathrm{fin}}$, let

$$
\ell(q)=\min\{|\sigma|:A_\sigma e_o=q\}.
$$

Here $\ell(q)$ measures the number of moves needed to realize the **entire
profile**, whereas $t(G,x,w)$ measures the shortest strategy maximizing a
single target value.

Define the alternating comparison vector

$$
\Lambda_m(q)=
\bigl(q(a_m),-q(a_{m-1}),q(a_{m-2}),\ldots,(-1)^m q(a_0)\bigr).
$$

The short-leaf coordinates $q(b),q(c)$ are omitted. Vectors are compared
lexicographically: at the first coordinate where they differ, the vector
with the smaller coordinate is smaller.

### Theorem 1: lexicographic extremality and an equality-case length bound

For every $q\in\mathcal R_{\mathrm{fin}}$,

$$
\Lambda_m(q)\le_{\mathrm{lex}}\Lambda_m(p_m).
$$

If $\Lambda_m(q)=\Lambda_m(p_m)$, then

$$
\ell(q)\ge m+2.
$$

Consequently, every $q\in\mathcal R_{m+1}$ satisfies

$$
\Lambda_m(q)<_{\mathrm{lex}}\Lambda_m(p_m).
$$

The equality hypothesis concerns only the alternating comparison vector;
it does not require $q=p_m$ on all vertices. Applying the length bound to
$p_m$ and using the reference construction gives $\ell(p_m)=m+2$.

### Theorem 2: explicit nonnegative integer weights

Set

$$
Q=4(m+3)^{2(m+2)},\qquad B=Q^{m-1},
$$

and define the initial weights

$$
\omega_m(a_i)=B+(-1)^{m-i}Q^i\quad(0\le i\le m),
\qquad
\omega_m(b)=\omega_m(c)=B.
$$

All these weights are nonnegative integers. For every
$q\in\mathcal R_{m+1}$,

$$
\langle q,\omega_m\rangle
<
\langle p_m,\omega_m\rangle.
$$

Thus this explicit linear objective strictly separates the reference
profile from every profile reachable in at most $m+1$ moves.

### Theorem 3: a lower bound on the shortest optimal length

For the graph and initial weights above,

$$
t(G_m,o,\omega_m)\ge m+2.
$$

Indeed, the reversed reference strategy $(\sigma_m^{\mathrm{ref}})^{\mathrm{rev}}$ has target
value $\langle p_m,\omega_m\rangle$, which exceeds the target value of every
strategy of length at most $m+1$. The theorem asserts a lower bound; it
does not assert that this particular $m+2$-step witness is globally optimal.

In particular, for every integer $K\ge0$, there exists $m\ge2$ such that

$$
\Delta(G_m)\le3
\qquad\text{and}\qquad
t(G_m,o,\omega_m)>K.
$$

Shortest optimal lengths are therefore unbounded even among trees of
maximum degree three, when the number of vertices is allowed to grow.

## 4. Paper 3: a uniform horizon and exact rational optimization

### Strategy operators and their convex hulls

Let $G$ have $n$ vertices. Regard each $A_\sigma$ as a real $n\times n$
matrix. Its entries are rational and nonnegative, and every row and column
sums to one. Define

$$
\mathcal A_k(G)=\{A_\sigma:|\sigma|\le k\},
\qquad
\mathcal A(G)=\bigcup_{k\ge0}\mathcal A_k(G),
$$

$$
\mathcal P_k(G)=\operatorname{conv}\mathcal A_k(G),
\qquad
\mathcal P(G)=\operatorname{conv}\mathcal A(G).
$$

All convex hulls here consist of finite convex combinations; no closure is
taken. A **rational polytope** means the real convex hull of a finite set
of rational matrices.

### Theorem 1.1: uniform convex-hull stabilization

For $n\ge2$, set

$$
r_n=\lceil\log_2 n\rceil,\qquad q_n=4n^2r_n.
$$

Define the uniform horizon by

$$
L_0=L_1=0,\qquad L_2=1,\qquad
L_n=2q_n(L_{n-1}+1)\quad(n\ge3).
$$

The convention $L_0=0$ covers the empty graph. For every finite graph $G$
on $n$ vertices,

$$
\mathcal P(G)=\mathcal P_{L_n}(G),
$$

and this common set is a rational polytope. Equivalently, every finite
strategy operator is a finite convex combination of strategy operators of
length at most $L_n$. It need not equal one individual short strategy operator.

For every $n\ge2$, the same recurrence satisfies the explicit bound

$$
L_n\le
16^{n-2}\left(\frac{n!}{2}\right)^2
\lceil\log_2 n\rceil^{\,n-2}.
$$

The asymptotic conclusion is

$$
L_n\le n^{(2+o(1))n}.
$$

Precisely, for every real $\varepsilon>0$, there exists an integer $N$
such that, for every integer $n\ge N$,

$$
L_n\le n^{(2+\varepsilon)n}.
$$

Both the explicit bound and this quantified asymptotic statement are proved.
The paper's intermediate finer logarithmic expansion is not separately
formalized.

### Corollary 1.2: short optimizers for every linear objective

For any real coefficient matrix $C=(C_{ij})$, define

$$
F_C(M)=\sum_{i,j\in V}C_{ij}M_{ij}.
$$

Then

$$
\sup_{\sigma}F_C(A_\sigma)
=
\max_{|\sigma|\le L_n}F_C(A_\sigma).
$$

In particular, there exists a legal strategy of length at most $L_n$ that
maximizes this objective over all finite legal strategies. The coefficients
$C_{ij}$ may have either sign, and the maximizing strategy may depend on $C$.

Taking $C_{ij}=\mathbf 1_{\{i=x\}}w(j)$ gives the single-target consequence:
for every nonnegative initial vector $w$ and every target $x$,

$$
t(G,x,w)\le L_n.
$$

This bound depends only on the number of vertices, uniformly over the graph,
the initial water levels, and the target.

### Proposition 7.1: the formalized exact-search and decision conclusions

Suppose the graph is given on a finite labelled vertex set and
$w:V\to\mathbb Q_{\ge0}$. Enumerate the connected vertex sets of size at
least two and all strategies using these sets of length at most $L_n$,
including the empty strategy. Evaluate their target values with exact
rational arithmetic and retain a maximizing strategy $\sigma_*$.

The implemented search returns a legal strategy satisfying

$$
|\sigma_*|\le L_n,
\qquad
(A_{\sigma_*}w)(x)=w^*(G,x,w).
$$

Its output value is rational and equals the unrestricted supremum in the
real-valued model. For any rational threshold $a$, the implemented Boolean
test satisfies

$$
\operatorname{exceedsThreshold}(G,w,x,a)=\mathrm{true}
\quad\Longleftrightarrow\quad
\exists\,\sigma\text{ legal},\ (A_\sigma w)(x)>a.
$$

The comparison is strict. These are correctness and decidability results
for the single-target search. Binary bit-complexity bounds, NEXP membership,
and an executable search for a general matrix objective are not formalized.

## 5. How the three papers fit together

Paper 1 establishes finite attainment and gives small bounds for paths and
star centers. Paper 2 shows that even degree-three trees can require
arbitrarily many moves as their size grows. Paper 3 gives a bound depending
only on the number of vertices.

These conclusions are compatible. For the explicit $n=m+3$ vertex examples
of Paper 2,

$$
n-1\le t(G_m,o,\omega_m)\le L_n.
$$

The lower bound rules out a constant bound based only on maximum degree;
the upper bound supplies a finite search horizon for each fixed graph size.

## 6. Correspondence with the Lean entry points

The following 15 declarations expose the main results above. Definitions in
the entry files are transparent aliases of the shared implementation;
detailed proofs and auxiliary lemmas remain in the corresponding directories.

| Paper result | Public declaration |
| --- | --- |
| Paper 1, Theorem 2.1 | `WaterTransport1.theorem_2_1` |
| Paper 1, Corollary 2.1 | `WaterTransport1.corollary_2_1` |
| Paper 1, Theorem 3.1 | `WaterTransport1.theorem_3_1` |
| Paper 1, Theorem 4.1 | `WaterTransport1.theorem_4_1` |
| Paper 2, Theorem 1, all three clauses | `WaterTransport2.theorem_1` |
| Paper 2, Theorem 2 | `WaterTransport2.theorem_2` |
| Paper 2, Theorem 3 | `WaterTransport2.theorem_3` |
| Paper 2, unboundedness consequence | `WaterTransport2.theorem_3_unbounded` |
| Paper 3, Theorem 1.1, stabilization and rationality | `WaterTransport3.theorem_1_1` |
| Paper 3, Theorem 1.1, explicit bound | `WaterTransport3.theorem_1_1_bound` |
| Paper 3, Theorem 1.1, asymptotic bound | `WaterTransport3.theorem_1_1_asymptotic` |
| Paper 3, Corollary 1.2, matrix objective | `WaterTransport3.corollary_1_2` |
| Paper 3, Corollary 1.2, target-length bound | `WaterTransport3.corollary_1_2_target` |
| Paper 3, Proposition 7.1, exact optimization | `WaterTransport3.proposition_7_1_exact` |
| Paper 3, Proposition 7.1, threshold decision | `WaterTransport3.proposition_7_1_threshold` |

All current declarations of Papers 1 and 2 have no `sorry` dependencies.
Paper 3's seven pending declarations belong to its separate repetition
example, described below; none is used by the 15 main declarations above.

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
`WaterTransport.lean` imports all three main files. The individual main files
contain the definition guides and numbered theorem statements listed above;
they also remain the library entry points used by Lake and the audits.

The review-facing namespaces are `WaterTransport1`, `WaterTransport2`, and
`WaterTransport3`. Existing implementation declarations remain available in
`WaterTransport`, `WaterTransport.Paper2`, and `WaterTransport.Paper3`.
Importing a main file also makes its supporting modules available.

## Supporting proof modules

File numbers give a reading order compatible with imports; they are not the
section numbers of the papers. Later papers reuse the first paper's model.

| Modules | Purpose |
| --- | --- |
| `WaterTransport1/S01`–`S02` | States, connected-set averaging, strategies, optimality, reverse profiles, and exact rational execution. |
| `WaterTransport1/S03`–`S05` | Analysis, attainment of optimal values, and the shortest optimal length. |
| `WaterTransport1/S06`–`S08` | Path geometry, shortening, and the public path theorems. |
| `WaterTransport1/S09` | The star algorithm and its optimality. |
| `WaterTransport1/S10`–`S11` | Finite certificate checkers, their soundness, and Examples 4.1 and 4.2. |
| `WaterTransport2/S01`–`S04` | The spider construction, barriers, lexicographic comparisons, and the length lower bound. |
| `WaterTransport3/S01`–`S03` | Operators, local geometry, and the uniform bound. |
| `WaterTransport3/S04` | The five-vertex repetition example, including the explicitly deferred certificates. |
| `WaterTransport3/S05` | Exact search for rational input and its correctness. |

## Deferred Section 6 certificates

Theorem 1.3 of Paper 3 concerns a five-vertex example where every optimal
strategy repeats a nontrivial selected set. Here **repetition-free** means
that no set of size at least two occurs twice; singleton identity moves
are ignored. This theorem is not among the verified main results above.

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
the main-file aliases and theorems and private helpers, for transitive axiom dependencies. Only `propext`,
`Classical.choice`, and `Quot.sound` are accepted. It also checks the preserved
statements and definitions and several model boundary cases.

[`AuditProgress.lean`](AuditProgress.lean) checks Papers 2 and 3,
including their main-file aliases and theorems. It permits
`sorryAx` only for the seven explicitly named pending declarations above;
any other declaration depending on `sorryAx` causes the audit to fail.

The fixed baselines in [`Research`](Research) are inputs to the declaration
checks. The original 223-entry Paper 1 baseline is unchanged: the audit preserves
the 207 retained declarations and requires the 16 explicitly listed Example 4.3
declarations to be absent. All 140 baseline declarations from Papers 2 and 3
remain checked. Do not regenerate the baselines to make an altered mathematical
statement pass.

Finite numerical certificates use exact arithmetic and Lean kernel checks.
There are no project-specific axioms asserting the results of an external
program.

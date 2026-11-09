# Erdős Problem 881, case k = 2: an informal proof

This note gives the mathematical argument behind [`K2.lean`](K2.lean) in ordinary language, so the
idea can be judged without reading Lean. The Lean file is the verified source: every lemma below
names the `K2.lean` declaration it corresponds to (all in the namespace `Erdos881K2`), and nothing
here goes beyond what the Lean proof does. The result is registered on Palomar as
[PALOMAR-2026-11-09-000017](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-09-000017).

## 1. Definitions

Throughout, $A, B, C, D$ are subsets of $\mathbb{N} = \{0, 1, 2, \dots\}$, and $0$ may belong to
$A$.

**Sumsets.** For $h \ge 0$, the $h$-fold sumset is
$$hA = \{a_1 + \dots + a_h : a_1, \dots, a_h \in A\},$$
sums of *exactly* $h$ elements of $A$, repetitions allowed. We write $A + A = 2A$.

**Asymptotic basis.** $A$ is an *asymptotic additive basis of order $h$* if all but finitely many
$n \in \mathbb{N}$ lie in $hA$, that is, there is $N$ with $n \in hA$ for every $n \ge N$.
(Lean: `Set.IsAsymptoticAddBasisOfOrder h`, from formal-conjectures.)

Two standard facts are used:

* *Monotonicity.* If $A$ is an asymptotic basis of order $m$ and $m \le n$, it is one of order $n$:
  fix $a \in A$; if every $k \ge N$ lies in $mA$, every $k \ge N + (n - m)a$ lies in $nA$.
  (formal-conjectures: `IsAsymptoticAddBasisOfOrder.mono`.)
* *Tail coverage.* We say $A$ *covers the tail from $N$ at order $h$* if every $n \ge N$ lies in
  $hA$ (Lean: `TailCovered h A N`).

**Minimality in Problem 881.** Following formal-conjectures
(`Erdos881.IsMinimalAsymptoticAddBasisOfOrder k A`), $A$ is a *minimal asymptotic basis of order
$k$* if

1. $A$ is an asymptotic basis of order $k$, and
2. for every **infinite** $B \subseteq A$, the set $A \setminus B$ is **not** an asymptotic basis of
   order $k$.

Problem 881 asks whether every such $A$ contains an infinite $B$ with $A \setminus B$ an
asymptotic basis of order $k + 1$.

**Remark (at most $h$ summands).** If "basis of order $h$" is read as "sums of at most $h$
elements", the results below still hold: apply them to $A \cup \{0\}$ and remove $0$ from the
deleted set.

## 2. Results

**Theorem 1** (`infinite_deletion_of_two_basis`). Let $A$ be an asymptotic basis of order 2. Then
there is an infinite $B \subseteq A$ such that $A \setminus B$ is an asymptotic basis of order 3.
No minimality is assumed.

**Corollary 2** (`erdos_881_two`; the case $k = 2$ of `Erdos881.erdos_881`). If $A$ is a minimal
asymptotic basis of order 2 in the sense of §1, then some infinite $B \subseteq A$ leaves
$A \setminus B$ an asymptotic basis of order 3.

*Proof.* Condition 1 of minimality says $A$ is a basis of order 2; apply Theorem 1. $\square$

**Corollary 3** (`not_minimal_three_of_two_basis`). If $A$ is an asymptotic basis of order 2, then
some proper subset $C \subsetneq A$ is an asymptotic basis of order 3. Hence no asymptotic basis of
order 2 is a minimal asymptotic basis of order 3 in the ordinary sense (no proper subset is a basis
of order 3).

*Proof.* Take $B$ from Theorem 1 and $C = A \setminus B$. Since $B$ is infinite it is nonempty, and
$B \subseteq A$, so $C \ne A$. $\square$

**Corollary 4** (`not_two_basis_of_minimal_high_order`). For $k \ge 3$, a set that is minimal of
order $k$ in the sense of Problem 881 is not an asymptotic basis of order 2.

*Proof.* If it were, Theorem 1 gives an infinite $B$ with $A \setminus B$ a basis of order 3, hence
of order $k$ by monotonicity, contradicting minimality. $\square$

The rest of this note proves Theorem 1. The proof splits on whether some positive difference
occurs infinitely often in $A$.

**Definition** (`hasInfiniteGaps`). $A$ has *infinite gaps* if for every $d > 0$ the set
$$P_d = \{b \in A : b + d \in A\}$$
is finite.

* **Case 1** ($A$ does not have infinite gaps): §4, `infinite_deletion_of_not_infinite_gaps`.
* **Case 2** ($A$ has infinite gaps): §5–§6, `infinite_deletion_of_finite_support_fusion`
  together with `not_tail_trap_of_sparse_two`.

## 3. Three combinatorial lemmas

**Lemma 3.1** (`basis_infinite`). Every asymptotic basis of order $h$ is infinite.

*Proof.* If $A \subseteq [0, M]$, then $hA \subseteq [0, hM]$, so no $n > hM$ lies in $hA$. $\square$

**Lemma 3.2** (`infinite_free_subset`). Let $S \subseteq \mathbb{N}$ be infinite and let $f$ assign
to each $b \in S$ a finite set $f(b)$ with $|f(b)| \le d$ and $b \notin f(b)$. Then there is an
infinite $T \subseteq S$ that is *free*: $c \notin f(b)$ for all $b, c \in T$.

*Proof.* Induction on $d$. For $d = 0$ take $T = S$.

For the step $d \to d + 1$, suppose first that some $a$ lies in $f(b)$ for infinitely many
$b \in S$. Let $S' = \{b \in S : a \in f(b)\}$ and $f'(b) = f(b) \setminus \{a\}$, so
$|f'(b)| \le d$. By induction there is an infinite free $T \subseteq S'$ for $f'$. It is free for
$f$ too: $c \in T$ cannot equal $a$, since then $a = c \in f(c)$, against $c \notin f(c)$; so
$c \in f(b)$ would give $c \in f'(b)$.

Otherwise every $a$ lies in $f(b)$ for only finitely many $b \in S$. Then for any finite
$t \subseteq S$ the set
$$t \;\cup\; \bigcup_{b \in t} \bigl(f(b) \cup \{c \in S : b \in f(c)\}\bigr)$$
is finite, so some $c \in S$ avoids it. Choosing $c_0, c_1, c_2, \dots$ greedily this way (each
$c_j$ avoiding the set built from $t = \{c_0, \dots, c_{j-1}\}$) gives distinct elements with
$c_j \notin f(c_i)$ and $c_i \notin f(c_j)$ for $i < j$, and $c_i \notin f(c_i)$ by hypothesis.
Take $T = \{c_0, c_1, \dots\}$. $\square$

**Lemma 3.3** (`infinite_residue_part`). An infinite $S \subseteq \mathbb{N}$ has, for each
$m > 0$, an infinite subset contained in a single residue class mod $m$. (Pigeonhole.) $\square$

## 4. Case 1: a positive difference occurs infinitely often

Here two fixed elements $x \ne y$ of $A$ serve as "switches".

**Definition** (`twoSwitchCandidates`). For $x, y \in \mathbb{N}$, a *candidate* is $b \in A$ with
$b \ne x$, $b \ne y$, and
$$b + x \in (A \setminus \{b\}) + (A \setminus \{b\}), \qquad
  b + y \in (A \setminus \{b\}) + (A \setminus \{b\}).$$

**Lemma 4.1** (`infinite_two_switch_candidates_of_repeated_gap`). If $d > 0$ and $P_d$ is infinite,
there are $x \ne y$ in $A$ with infinitely many candidates.

*Proof.* Pick $u < v$ in $P_d$ and set $x = u + d$, $y = v + d$; both lie in $A$ and $x \ne y$. For
every $b \in P_d \setminus \{u, v, u + d, v + d\}$,
$$b + x = (b + d) + u, \qquad b + y = (b + d) + v,$$
where $b + d, u, v \in A$ all differ from $b$ (as $d > 0$), and $b \ne x, y$. So all these
infinitely many $b$ are candidates. $\square$

**Lemma 4.2** (`missing_three_forces_deleted_pair`). Suppose every $m \ge N$ lies in $A + A$, let
$C$ be any set with $x \in C$, and suppose $b + x \in C + C$ for every $b \in A \setminus C$. If
$n \ge N + x$ and $n \notin 3C$, then $n = x + u + v$ with $u, v \in A \setminus C$.

*Proof.* Write $n - x = u + v$ with $u, v \in A$. If $u, v \in C$, then $n = u + v + x \in 3C$. If
$u \in C$ but $v \notin C$, write $v + x = p + q$ with $p, q \in C$; then $n = u + p + q \in 3C$.
The case $v \in C$, $u \notin C$ is symmetric. So $u, v \notin C$. $\square$

**Lemma 4.3** (`three_basis_of_two_shift_switches`). Let $A$ be an asymptotic basis of order 2 and
let $x, y \in C$ satisfy

* $b + x \in C + C$ and $b + y \in C + C$ for every $b \in A \setminus C$, and
* $x + u + v \ne y + p + q$ for all $u, v, p, q \in A \setminus C$.

Then $C$ is an asymptotic basis of order 3.

*Proof.* Let every $m \ge N$ lie in $A + A$. If $n \ge N + x + y$ and $n \notin 3C$, Lemma 4.2
applied with $x$ and with $y$ gives $n = x + u + v = y + p + q$ with $u, v, p, q \in A \setminus C$,
contradicting the second hypothesis. $\square$

**Proposition 4.4** (`infinite_deletion_of_two_switch_candidates`). If $A$ is an asymptotic basis
of order 2 and $x \ne y$ in $A$ have infinitely many candidates, then some infinite $B \subseteq A$
leaves $A \setminus B$ an asymptotic basis of order 3.

*Proof (construction of $B$).* Let $S$ be the set of candidates. For each $b \in S$ fix
$u_b, v_b, p_b, q_b \in A \setminus \{b\}$ with $u_b + v_b = b + x$ and $p_b + q_b = b + y$, and
put $f(b) = \{u_b, v_b, p_b, q_b\}$. Then $|f(b)| \le 4$ and $b \notin f(b)$, so Lemma 3.2 gives an
infinite free $T \subseteq S$. With $m = x + y + 1$, Lemma 3.3 gives an infinite
$B \subseteq T$ inside one residue class mod $m$. Let $C = A \setminus B$; then
$A \setminus C = B$. We check the hypotheses of Lemma 4.3.

* $x, y \in C$: they are in $A$, and no candidate equals $x$ or $y$.
* *Switches survive.* For $b \in B$, the witnesses $u_b, v_b, p_b, q_b$ are in $A$, and none lies
  in $B$ because $B \subseteq T$ is free. So they lie in $C$, and $b + x, b + y \in C + C$.
* *No collision.* If $x + u + v = y + p + q$ with $u, v, p, q \in B$, then $u \equiv p$ and
  $v \equiv q \pmod m$, so $x \equiv y \pmod m$. As $0 \le x, y < m$, this forces $x = y$, a
  contradiction.

By Lemma 4.3, $C = A \setminus B$ is an asymptotic basis of order 3, and $B$ is infinite. $\square$

**Theorem 4.5** (`infinite_deletion_of_not_infinite_gaps`). If $A$ is an asymptotic basis of order
2 without infinite gaps, Theorem 1 holds for $A$.

*Proof.* Some $P_d$ with $d > 0$ is infinite; combine Lemma 4.1 and Proposition 4.4. $\square$

## 5. A greedy deletion scheme (any order $h$)

Case 2 deletes elements one at a time. This section isolates the bookkeeping; it works for any $h$.

**Definition** (`SupportFusionState`, `FiniteSupportFusion`). A *state* is a triple
$s = (D_s, P_s, F_s)$: a finite set $D_s$ of deleted elements, a finite set $P_s$ of *protected*
elements, and a *frontier* $F_s \in \mathbb{N}$. We say the greedy scheme *runs* for $(h, A)$ if
there are a threshold $N$ and a predicate "good" on states such that

1. $(\emptyset, \emptyset, N)$ is good;
2. every good $s$ has $D_s \subseteq A$, $D_s \cap P_s = \emptyset$, and every $n$ with
   $N \le n < F_s$ lies in $h(A \cap P_s)$;
3. every good $s$ has a good successor $t$ with $D_s \subsetneq D_t$, $P_s \subseteq P_t$ and
   $F_s < F_t$.

**Proposition 5.1** (`infinite_deletion_of_finite_support_fusion`). If the greedy scheme runs for
$(h, A)$, there is an infinite $B \subseteq A$ with $A \setminus B$ an asymptotic basis of order
$h$.

*Proof.* Starting from $s_0 = (\emptyset, \emptyset, N)$, choose good successors
$s_0, s_1, s_2, \dots$ and let $B = \bigcup_i D_{s_i} \subseteq A$.

* $B$ is infinite, since $|D_{s_i}| \ge i$.
* *Protected elements are never deleted:* $A \cap P_{s_i} \subseteq A \setminus B$ for every $i$.
  If $b \in P_{s_i} \cap D_{s_j}$, then for $j \ge i$ we get $b \in P_{s_j} \cap D_{s_j}$, and for
  $j \le i$ we get $b \in D_{s_i} \cap P_{s_i}$; both are empty.
* *Coverage.* The frontiers strictly increase from $N$, so $F_{s_{n+1}} > n$. For $n \ge N$,
  property 2 gives $n \in h(A \cap P_{s_{n+1}}) \subseteq h(A \setminus B)$. $\square$

What can stop the scheme is a *trap*.

**Definitions** (`tailRedundant`, `TailTrapAbove`). If $C$ covers the tail from $N$ at order $h$,
an element $a \in C$ is *redundant* if $C \setminus \{a\}$ still covers the tail from $N$ at order
$h$. A *trap above $L$* for $(h, A, N)$ is a finite $D \subseteq A$ with all elements $\ge L$ such
that $A \setminus D$ covers the tail from $N$ at order $h$ but has only finitely many redundant
elements.

**Lemma 5.2** (`infinite_free_subset_avoiding`). Lemma 3.2 still holds with $T$ additionally
disjoint from a given finite set $P$. (Apply Lemma 3.2 to $S \setminus P$.) $\square$

**Lemma 5.3** (`simultaneous_full_witness_avoidance`). Let $S$ be infinite, $P$ finite, and
$q : \mathbb{N} \to \mathbb{N}$ with $q(b) \in h(C \setminus \{b\})$ for each $b \in S$. Then there
is an infinite $T \subseteq S$, disjoint from $P$, with $q(b) \in h(C \setminus T)$ for each
$b \in T$.

*Proof.* Fix a representation of $q(b)$ by $h$ elements of $C \setminus \{b\}$ and let $f(b)$ be
its set of summands: $|f(b)| \le h$ and $b \notin f(b)$. Lemma 5.2 gives a free $T$ disjoint from
$P$, and freeness says the representation of $q(b)$ avoids $T$. $\square$

**Proposition 5.4** (`finite_support_fusion_of_no_tail_trap`). If $A$ covers the tail from $N$ at
order $h$ and there is no trap above $L$ for $(h, A, N)$, the greedy scheme runs for $(h, A)$.

*Proof.* Call a state $s = (D, P, F)$ good if $D \subseteq A$, every element of $D$ is $\ge L$,
$D \cap P = \emptyset$, $A \setminus D$ covers the tail from $N$ at order $h$, $F \ge N$, and every
$n \in [N, F)$ lies in $h(A \cap P)$. The initial state $(\emptyset, \emptyset, N)$ is good, and
property 2 is part of the definition.

*Extension.* Let $s = (D, P, F)$ be good and $C = A \setminus D$. Since $D$ is not a trap, $C$ has
infinitely many redundant elements, and infinitely many of them are $\ge L$; call that set $S$.
For $b \in S$, redundancy and $F \ge N$ give $F \in h(C \setminus \{b\})$. Lemma 5.3 (with
$q \equiv F$ and the protected set $P$) yields an infinite $T \subseteq S$ disjoint from $P$ such
that, for $b \in T$, $F$ has a representation in $h(C \setminus T)$. Fix one $b \in T$ (only one
is used), and a representation $F = w_1 + \dots + w_h$ with $w_i \in C$, $w_i \ne b$. Let
$W = \{w_1, \dots, w_h\}$ and
$$t = (D \cup \{b\},\; P \cup W,\; F + 1).$$
Then $t$ is good:

* $b \in A$, $b \ge L$, and $b \notin D$ (as $b \in C$), so $D \subsetneq D \cup \{b\}$.
* Disjointness: $b \notin P$ (as $T \cap P = \emptyset$), $b \notin W$, $D \cap P = \emptyset$, and
  $W \subseteq C$ is disjoint from $D$.
* $A \setminus (D \cup \{b\}) = C \setminus \{b\}$ covers the tail from $N$, because $b$ is
  redundant in $C$.
* Every $n \in [N, F)$ lies in $h(A \cap P) \subseteq h(A \cap (P \cup W))$, and $F$ lies in
  $h(A \cap W)$. $\square$

In words: each step deletes one redundant element above $L$, chooses a representation of the
current frontier that avoids it, protects that representation's summands forever, and moves the
frontier up by one. Coverage is always measured from the same threshold $N$.

## 6. Case 2: infinite gaps leave no trap at order 3

From now on $A$ is an asymptotic basis of order 2 with infinite gaps.

**Lemma 6.1** (`translate_intersection_bounded`). For $x \ne y$ there is $M$ such that whenever
$u, v \in A$ and $x + u = y + v$, we have $x + u \le M$.

*Proof.* Say $x < y$. Then $u = v + (y - x)$, so $v \in P_{y - x}$, which is finite, say bounded by
$M'$. Take $M = y + M'$. The case $x > y$ is symmetric. $\square$

**Lemma 6.2** (`eventually_not_two_stem_hits`). Let $D$ be finite and $x + \max D < y$ (with
$\max \emptyset = 0$). There is $U$ such that no $n \ge U$ has both forms
$$n = x + d + u \quad\text{and}\quad n = y + e + v \qquad (d, e \in D,\ u, v \in A).$$

*Proof.* For $d, e \in D$ we have $x + d \le x + \max D < y \le y + e$, so $x + d \ne y + e$.
Lemma 6.1 bounds every coincidence $(x + d) + u = (y + e) + v$ by some $M_{d,e}$. Take
$U = 1 + \max_{d, e} M_{d,e}$. $\square$

**Lemma 6.3** (`private_target_of_not_tailRedundant`). If $C$ covers the tail from $N$ at order
$h$ and $a \in C$ is not redundant, there is $n \ge N$ with $n \ge a$, $n \in hC$, and every
representation of $n$ as a sum of $h$ elements of $C$ uses $a$.

*Proof.* Some $n \ge N$ is missing from $h(C \setminus \{a\})$, but $n \in hC$. Every representation
of $n$ in $hC$ must therefore use $a$, so $a \le n$. $\square$

**Lemma 6.4** (`missing_triple_anchor_alternative`). Suppose every $m \ge T$ lies in $A + A$, $D$
is finite, $b \in A \setminus D$, $b \ne a$, $n \ge T + b$, and
$n \notin 3\bigl((A \setminus D) \setminus \{a\}\bigr)$. Then

* $n = b + d + u$ for some $d \in D$, $u \in A$ (call $b$ *bad* for $n$), or
* $n = b + a + u$ for some $u \in A$ (call $b$ a *petal* for $n$).

*Proof.* Write $n - b = u + v$ with $u, v \in A$. If $u$ or $v$ lies in $D$, $b$ is bad. If $u$ or
$v$ equals $a$, $b$ is a petal. Otherwise $b, u, v \in (A \setminus D) \setminus \{a\}$ and
$n = b + u + v$, a contradiction. $\square$

**Theorem 6.5** (`infinite_tailRedundant_of_sparse_two`). Let $A$ be an asymptotic basis of order 2
with infinite gaps, $D \subseteq A$ finite, and suppose $C = A \setminus D$ covers the tail from $N$
at order 3. Then $C$ has infinitely many redundant elements at order 3.

*Proof.* Let every $m \ge T$ lie in $A + A$. By Lemma 3.1, $C$ is infinite. Write
$\delta = \max D$. Choose five *anchors* in $C$:

* $x \in C$; $y \in C$ with $y > x + \delta$; $z \in C$ with $z > y + \delta$;
* $M = M_{xy} + M_{xz} + M_{yz}$, where $M_{xy}, M_{xz}, M_{yz}$ are the bounds of Lemma 6.1 for
  the pairs $(x, y)$, $(x, z)$, $(y, z)$;
* $p \in C$ with $p > M + z$; $q \in C$ with $q > p + \delta$.

Let $U_{xy}, U_{xz}, U_{yz}, U_{pq}$ be the bounds of Lemma 6.2 for the pairs $(x,y)$, $(x,z)$,
$(y,z)$, $(p,q)$, which are all separated by more than $\delta$, and set
$$K = T + x + y + z + p + q + U_{xy} + U_{xz} + U_{yz} + U_{pq} + M + 1.$$

We claim every $a \in C$ with $a \ge K$ is redundant; since $C$ is infinite, this proves the
theorem. Suppose $a \ge K$ is not redundant. Lemma 6.3 gives a target $n \ge a \ge K$ with
$n \notin 3(C \setminus \{a\})$. Each anchor $b \in \{x, y, z, p, q\}$ satisfies $b < K \le a$ and
$n \ge T + b$, so by Lemma 6.4 each anchor is bad or a petal for $n$. A petal $b$ means
$b + u = n - a$ for some $u \in A$.

* *Bound on $n - a$.* Since $n \ge U_{xy}, U_{xz}, U_{yz}$, no two of $x, y, z$ are both bad
  (Lemma 6.2). So at least two of them are petals, say $b \ne b'$, with
  $b + u = b' + u' = n - a$. Lemma 6.1 gives $n - a \le M_{bb'} \le M$.
* *Contradiction.* Since $n \ge U_{pq}$, $p$ and $q$ are not both bad, so one of them, call it
  $c$, is a petal: $c + u = n - a$ with $u \ge 0$. Then $c \le n - a \le M$, but
  $q > p > M + z \ge M$. $\square$

In words: removing a single large element $a$ can only destroy targets $n$ that are "close" to
$a$ ($n - a$ bounded), because three far-apart anchors cannot all fall into the finite deleted
stem $D$, and two petals pin $n - a$ down. Two still larger anchors then make even those targets
impossible.

**Corollary 6.6** (`not_tail_trap_of_sparse_two`). If $A$ is an asymptotic basis of order 2 with
infinite gaps, there is no trap at order 3 for any $N$ and $L$.

*Proof.* A trap $D$ would have finitely many redundant elements, contradicting Theorem 6.5. $\square$

## 7. Proof of Theorem 1

Let $A$ be an asymptotic basis of order 2.

* If $A$ does not have infinite gaps, apply Theorem 4.5.
* If $A$ has infinite gaps, $A$ is an asymptotic basis of order 3 by monotonicity, so it covers the
  tail from some $N$ at order 3. By Corollary 6.6 there is no trap above $L = 0$, so the greedy
  scheme runs (Proposition 5.4), and Proposition 5.1 gives an infinite $B \subseteq A$ with
  $A \setminus B$ an asymptotic basis of order 3. $\square$

## 8. Relation to the literature

Problem 881 is listed on [erdosproblems.com/881](https://www.erdosproblems.com/881) and stated in
Lean as `Erdos881.erdos_881` in google-deepmind/formal-conjectures; the general problem is open, and
the cases $k \ge 3$ remain open.

Erdős and Nathanson, *Minimal asymptotic bases for the natural numbers*, J. Number Theory 12 (1980),
p. 155, asked whether a minimal asymptotic basis of order 3 can be an asymptotic basis of order 2,
and proved the corresponding statement for order 4. Corollary 3 answers their order-3 question in
the negative.

An unrefereed manuscript posted on the problem's forum on 2026-05-03, *Infinite Deletions from
Strongly Minimal Additive Bases*, states Corollary 3 as its Proposition 12 with a proof sketch,
which we have not checked; that claim predates ours. The same manuscript claims a counterexample
to Problem 881 for every $k \ge 2$, under the same "exactly $k$ summands" convention, so Theorem 1
rules out its claim for $k = 2$. For Theorem 1 and Corollary 2 we found no earlier proof in the
sources we checked; see [README.md](README.md) for details.

## 9. Verification

The argument above is checked by the Lean kernel in [`K2.lean`](K2.lean); see
[README.md](README.md#check-it) for how to build it and print the axioms used. Palomar entry:
[PALOMAR-2026-11-09-000017](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-09-000017).

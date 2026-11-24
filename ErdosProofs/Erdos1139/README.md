# Erdős Problem 1139

[Problem 1139](https://www.erdosproblems.com/1139): let `1 ≤ u₁ < u₂ < ⋯` be the integers with at
most two prime factors, counted with multiplicity. Is it true that

    limsup_{k → ∞} (u_{k+1} − u_k) / log k = ∞ ?

[`Main.lean`](Main.lean) proves that it is:

| Theorem | Statement |
| --- | --- |
| `Erdos1139Proof.erdos_1139` | `limsup_{k → ∞} (u (k + 1) − u k) / log (k + 1) = ⊤` in `EReal`, where `u = Nat.nth (fun n ↦ 0 < n ∧ Ω n ≤ 2)`. This is the statement of `Erdos1139.erdos_1139` in formal-conjectures. |
| `Erdos1139Proof.erdos_1139_fc` | The formal-conjectures theorem `Erdos1139.erdos_1139` itself. |

The formal statement indexes from 0 and includes `u = 1` (since `Ω 1 = 0`), and divides by
`log (k + 1)` instead of `log k`. Neither changes the limsup. Each quotient is a finite real number
cast to `EReal`, so the limsup is `⊤` exactly when the gaps are unbounded relative to `log k`.

## Prior work

The problem is listed as open on erdosproblems.com (last edited 23 January 2026). On the
problem's [forum thread](https://www.erdosproblems.com/forum/thread/1139), a proof by GPT Pro was
posted on 19 June 2026, and a screening check found no issues. That proof covers the offsets with
a hypergraph built from linear forms in primes, and uses the Green–Tao theorem on linear equations
in primes for its first- and second-moment counts. The thread also records earlier work by
Chojecki, gavinsherry and Tao, and the connection to [Problem 689](https://www.erdosproblems.com/689).

The proof here was found independently, without access to the forum or the internet, and takes a
different route: it uses no results on linear equations in primes, only elementary sieve bounds,
smooth-number counts and a second-moment argument, all proved in the file. As far as we know it
is the first machine-checked proof of the statement. If you know of an earlier one, please open
an issue.

## How the proof works

The names below are the lemmas in [`Main.lean`](Main.lean).

1. **Reduction** (`large_holes`, `erdos_1139`). For every `η > 0` there are arbitrarily large `y`
   and `N ≥ y` with `log (N + 1) ≤ η y` such that every number `N + h`, `1 ≤ h ≤ y`, has more than
   two prime factors. If `u_k ≤ N < N + y < u_{k+1}`, then `k ≤ N`, so
   `(u_{k+1} − u_k) / log (k + 1) ≥ 1 / η`. Since `η` is arbitrary, the limsup is infinite.
2. **Construction of `N`** (`hole_from_cover`, `crt_squares`). `N` comes from the Chinese remainder
   theorem, in the style of the Erdős–Rankin constructions for long prime gaps. Each `N + h` gets a
   divisor `d < N + h` with `Ω d = 2`, either a product of two primes assigned to `h` or the
   square of a prime, so `Ω (N + h) > 2`. The modulus is small enough that `log (N + 1)` is at most
   about `4x`, where `x` bounds the primes used, plus a term for the patched offsets.
3. **Kinds of offsets** (`offset_classification`). With thresholds `H < w ≤ z`, every offset
   `1 ≤ h ≤ y` is one of three kinds:
   - `(w + 1)`-smooth, or a prime above `z` times a number at most `H`. These need two hits by small
     primes.
   - A prime in `(w, z]` times a smooth number. These need one hit by a small prime or by a
     prime from a band.
   - Divisible by two primes in `(w, z]`. These are covered by those two primes.
4. **Choosing the residues** (`choose_cover`). The residues of the primes up to `w` are chosen by
   averaging over all assignments, with Euler-product weights and smooth-number bounds. The larger
   primes, in `(z, x]`, are grouped into bands (`Band`); a second-moment and Cauchy–Schwarz
   estimate (`band_moments`, `band_cauchy`) shows that some choice of residues covers almost
   every remaining offset. The averaging leaves a small set `F` of uncovered offsets.
5. **Patching** (`enough_patch_primes`). Each offset in `F` gets the square of its own prime in
   `(y, y²]`. `F` is small enough that this keeps `log (N + 1) ≤ η y`.

## Check it

From the repository root:

```bash
lake exe cache get
lake build ErdosProofs.Erdos1139.Axioms
```

The build prints the axioms of both theorems. Each lists only `propext`, `Classical.choice` and
`Quot.sound`.

## How this proof was found

The proof was found by one Codex CLI session running GPT-6.2-sol at maximum reasoning effort, in a
screening experiment of an automated proof-search framework. The
session was given only the formal statement and its definitions, with no network access, and was
not told that the problem is open. It found the proof in about 75 minutes, over two rounds, and the
Lean kernel checked it. The proof in this repository is the session's Lean code, ported from Lean
v4.27.0 to the toolchain of this repository; the comments and this README were written with Claude
(Anthropic). No human wrote the mathematical argument.

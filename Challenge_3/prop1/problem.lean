import Mathlib

/-
# Problem Description

Throughout, all variables denoting integers are positive integers unless stated otherwise.

This problem concerns a divisor-sum quantity `q_n` and a combinatorial model of
colored marked rectangles. The two main statements are:

* Lemma 1: `q_n` equals the signed count `|X_N^+| - |X_N^-|` (with `N = n + 1`).
* Lemma 2: there is an injection `X_N^- ↪ X_N^+`, hence `|X_N^-| ≤ |X_N^+|`, and
  therefore `q_n ≥ 0` for every `n ≥ 1`.

## Background and context

Definition 1 (Divisor-sum function). For an integer `m ≥ 1`,
  `σ(m) := ∑_{d ∣ m} d`, the sum of all positive divisors of `m`.

Definition 2 (The quantity `q_n`). For an integer `n ≥ 1`, set `N := n + 1` and define
  `q_n := (-1)^N σ(N) + 2 ∑_{r=1}^{N-1} (-1)^r σ(r)`.

  Remark (origin of `q_n`). In the source text, `q_n` is introduced as
  `q_n = -[t^n] P(t) S(t)`, where `P(t) = 1 + 2t + 2t^2 + ⋯` and
  `S(t) = ∑_{m≥0} (-1)^m σ(m+1) t^m`. Expanding the Cauchy product and substituting
  `N = n+1`, `r = m+1` yields the closed form above. We adopt this closed form as the
  definition of `q_n` so that the statements are self-contained. The two formulas are
  equal as integers; this equivalence is not a lemma to be proven here.

Definition 3 (The rectangle set `R_m`). For `m ≥ 1`,
  `R_m := { (a,b,i) : a,b ≥ 1, a*b = m, 1 ≤ i ≤ a }`.
  A triple `(a,b,i)` is an `a`-by-`b` rectangle with a marked row `i`.

Definition 4 (Color sets `E_N(m)`). For `N ≥ 2` and `m ≥ 1`,
  `E_N(m) = {0,1}` if `m < N`, and `E_N(m) = {0}` if `m = N`.
  (For `m > N` the set is not used; here it is the empty set.)

Definition 5 (The colored set `X_N`). For `N ≥ 2`,
  `X_N := { (a,b,i,ε) : a,b ≥ 1, a*b ≤ N, 1 ≤ i ≤ a, ε ∈ E_N(a*b) }`. This is finite.

Definition 6 (Sign / parity and the parts `X_N^+`, `X_N^-`). An element `(a,b,i,ε) ∈ X_N`
  is positive if its area `a*b` is even, and negative if `a*b` is odd.
  `X_N^+ := { x ∈ X_N : a*b even }`, `X_N^- := { x ∈ X_N : a*b odd }`. These partition `X_N`.

## Notes on Interpretation

* `q_n` is fixed by its closed form (Definition 2). It has been numerically verified to
  equal `|X_N^+| - |X_N^-|` for `1 ≤ n ≤ 14`.
* In Definition 2, the sum `∑_{r=1}^{N-1}` is empty when `N = 1`; but `N = n+1 ≥ 2`
  throughout, so this case does not arise for the main statements.
* All sets `R_m`, `X_N`, `X_N^±` are finite, so all cardinalities are finite natural
  numbers and the subtraction in Lemma 1 is an integer subtraction.
-/

open Finset

namespace ColoredRectangles

/-- Definition 1: the divisor-sum function `σ(m) = ∑_{d ∣ m} d`. -/
def sigmaSum (m : ℕ) : ℕ := ∑ d ∈ m.divisors, d

/-- Definition 3: the rectangle set `R_m` as a finite set of triples `(a, b, i)`
with `a*b = m` and `1 ≤ i ≤ a` (positivity of `a, b` follows from `a*b = m ≥ 1`,
but we keep the explicit conditions to match the informal statement). -/
def R (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 m ×ˢ Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter
    (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2.1 ∧ p.1 * p.2.1 = m ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ p.1)

/-- Definition 4: the color set `E_N(m)`, equal to `{0,1}` for `m < N`, `{0}` for
`m = N`, and (by convention, unused) `∅` for `m > N`. -/
def E (N m : ℕ) : Finset ℕ := if m < N then {0, 1} else if m = N then {0} else ∅

/-- Definition 5: the colored set `X_N` as a finite set of quadruples `(a, b, i, ε)`. -/
def X (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 0 1).filter
    (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2.1 ∧ p.1 * p.2.1 ≤ N ∧ 1 ≤ p.2.2.1 ∧ p.2.2.1 ≤ p.1 ∧
      p.2.2.2 ∈ E N (p.1 * p.2.1))

/-- Definition 6: the positive part `X_N^+` (elements of even area). -/
def Xpos (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) := (X N).filter (fun p => Even (p.1 * p.2.1))

/-- Definition 6: the negative part `X_N^-` (elements of odd area). -/
def Xneg (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) := (X N).filter (fun p => Odd (p.1 * p.2.1))

/-- Definition 2: the quantity `q_n`, with `N = n + 1`,
`q_n = (-1)^N σ(N) + 2 ∑_{r=1}^{N-1} (-1)^r σ(r)`. -/
def qn (n : ℕ) : ℤ :=
  let N := n + 1
  (-1) ^ N * (sigmaSum N : ℤ) + 2 * ∑ r ∈ Finset.Icc 1 (N - 1), (-1) ^ r * (sigmaSum r : ℤ)

/-- Supporting fact: `|R_m| = σ(m)` for every `m ≥ 1`. -/
theorem card_R (m : ℕ) (hm : 1 ≤ m) : (R m).card = sigmaSum m := by
  sorry

/-- The positive and negative parts partition `X_N` (they are disjoint). -/
theorem disjoint_Xpos_Xneg (N : ℕ) : Disjoint (Xpos N) (Xneg N) := by
  sorry

/-- The positive and negative parts cover `X_N`. -/
theorem Xpos_union_Xneg (N : ℕ) : Xpos N ∪ Xneg N = X N := by
  sorry

/-- **Lemma 1 (signed count).** For every integer `n ≥ 1`, with `N = n + 1`,
`q_n = |X_N^+| - |X_N^-|` as an equality of integers. -/
theorem q_signed_count (n : ℕ) (hn : 1 ≤ n) :
    qn n = ((Xpos (n + 1)).card : ℤ) - ((Xneg (n + 1)).card : ℤ) := by
  sorry

/-- **Lemma 2 (injection).** For every integer `N ≥ 2` there exists a map
`Φ : X_N^- → X_N^+` (modeled as a map on quadruples sending `X_N^-` into `X_N^+`)
that is injective on `X_N^-`. -/
theorem injection (N : ℕ) (hN : 2 ≤ N) :
    ∃ Φ : (ℕ × ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ × ℕ),
      (∀ x ∈ Xneg N, Φ x ∈ Xpos N) ∧ Set.InjOn Φ (Xneg N) := by
  sorry

/-- Consequence of Lemma 2: `|X_N^-| ≤ |X_N^+|`. -/
theorem card_Xneg_le_card_Xpos (N : ℕ) (hN : 2 ≤ N) :
    (Xneg N).card ≤ (Xpos N).card := by
  sorry

/-- **Corollary of Lemmas 1 and 2.** `q_n ≥ 0` for every integer `n ≥ 1`. -/
theorem qn_nonneg (n : ℕ) (hn : 1 ≤ n) : 0 ≤ qn n := by
  sorry

end ColoredRectangles

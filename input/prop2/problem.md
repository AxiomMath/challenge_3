Read `challenge3_Part2.tex`. From `challenge3_Part2.tex`, formalize and prove Proposition~\ref{prop:main}.

Please use the lean code below which contains the formalizations and proofs of Lemma~\ref{lem:q-signed-count} and Lemma~\ref{lem:injection}.


import Mathlib

/-
# Problem Description

Throughout, all variables denoting integers are positive integers unless stated otherwise.

This problem concerns a divisor-sum quantity `q_n` and a combinatorial model of
colored marked rectangles. The two main statements are:

* Lemma 1: `q_n` equals the signed count `|X_N^+| - |X_N^-|` (with `N = n + 1`).
* Lemma 2: there is an injection `X_N^- ? X_N^+`, hence `|X_N^-| ? |X_N^+|`, and
  therefore `q_n ? 0` for every `n ? 1`.

## Background and context

Definition 1 (Divisor-sum function). For an integer `m ? 1`,
  `?(m) := ?_{d ? m} d`, the sum of all positive divisors of `m`.

Definition 2 (The quantity `q_n`). For an integer `n ? 1`, set `N := n + 1` and define
  `q_n := (-1)^N ?(N) + 2 ?_{r=1}^{N-1} (-1)^r ?(r)`.

  Remark (origin of `q_n`). In the source text, `q_n` is introduced as
  `q_n = -[t^n] P(t) S(t)`, where `P(t) = 1 + 2t + 2t^2 + ?` and
  `S(t) = ?_{m?0} (-1)^m ?(m+1) t^m`. Expanding the Cauchy product and substituting
  `N = n+1`, `r = m+1` yields the closed form above. We adopt this closed form as the
  definition of `q_n` so that the statements are self-contained. The two formulas are
  equal as integers; this equivalence is not a lemma to be proven here.

Definition 3 (The rectangle set `R_m`). For `m ? 1`,
  `R_m := { (a,b,i) : a,b ? 1, a*b = m, 1 ? i ? a }`.
  A triple `(a,b,i)` is an `a`-by-`b` rectangle with a marked row `i`.

Definition 4 (Color sets `E_N(m)`). For `N ? 2` and `m ? 1`,
  `E_N(m) = {0,1}` if `m < N`, and `E_N(m) = {0}` if `m = N`.
  (For `m > N` the set is not used; here it is the empty set.)

Definition 5 (The colored set `X_N`). For `N ? 2`,
  `X_N := { (a,b,i,?) : a,b ? 1, a*b ? N, 1 ? i ? a, ? ? E_N(a*b) }`. This is finite.

Definition 6 (Sign / parity and the parts `X_N^+`, `X_N^-`). An element `(a,b,i,?) ? X_N`
  is positive if its area `a*b` is even, and negative if `a*b` is odd.
  `X_N^+ := { x ? X_N : a*b even }`, `X_N^- := { x ? X_N : a*b odd }`. These partition `X_N`.

## Notes on Interpretation

* `q_n` is fixed by its closed form (Definition 2). It has been numerically verified to
  equal `|X_N^+| - |X_N^-|` for `1 ? n ? 14`.
* In Definition 2, the sum `?_{r=1}^{N-1}` is empty when `N = 1`; but `N = n+1 ? 2`
  throughout, so this case does not arise for the main statements.
* All sets `R_m`, `X_N`, `X_N^�` are finite, so all cardinalities are finite natural
  numbers and the subtraction in Lemma 1 is an integer subtraction.
-/

open Finset

namespace ColoredRectangles

/-- Definition 1: the divisor-sum function `?(m) = ?_{d ? m} d`. -/
def sigmaSum (m : ?) : ? := ? d ? m.divisors, d

/-- Definition 3: the rectangle set `R_m` as a finite set of triples `(a, b, i)`
with `a*b = m` and `1 ? i ? a` (positivity of `a, b` follows from `a*b = m ? 1`,
but we keep the explicit conditions to match the informal statement). -/
def R (m : ?) : Finset (? � ? � ?) :=
  (Finset.Icc 1 m �? Finset.Icc 1 m �? Finset.Icc 1 m).filter
    (fun p => 1 ? p.1 ? 1 ? p.2.1 ? p.1 * p.2.1 = m ? 1 ? p.2.2 ? p.2.2 ? p.1)

/-- Definition 4: the color set `E_N(m)`, equal to `{0,1}` for `m < N`, `{0}` for
`m = N`, and (by convention, unused) `?` for `m > N`. -/
def E (N m : ?) : Finset ? := if m < N then {0, 1} else if m = N then {0} else ?

/-- Definition 5: the colored set `X_N` as a finite set of quadruples `(a, b, i, ?)`. -/
def X (N : ?) : Finset (? � ? � ? � ?) :=
  (Finset.Icc 1 N �? Finset.Icc 1 N �? Finset.Icc 1 N �? Finset.Icc 0 1).filter
    (fun p => 1 ? p.1 ? 1 ? p.2.1 ? p.1 * p.2.1 ? N ? 1 ? p.2.2.1 ? p.2.2.1 ? p.1 ?
      p.2.2.2 ? E N (p.1 * p.2.1))

/-- Definition 6: the positive part `X_N^+` (elements of even area). -/
def Xpos (N : ?) : Finset (? � ? � ? � ?) := (X N).filter (fun p => Even (p.1 * p.2.1))

/-- Definition 6: the negative part `X_N^-` (elements of odd area). -/
def Xneg (N : ?) : Finset (? � ? � ? � ?) := (X N).filter (fun p => Odd (p.1 * p.2.1))

/-- Definition 2: the quantity `q_n`, with `N = n + 1`,
`q_n = (-1)^N ?(N) + 2 ?_{r=1}^{N-1} (-1)^r ?(r)`. -/
def qn (n : ?) : ? :=
  let N := n + 1
  (-1) ^ N * (sigmaSum N : ?) + 2 * ? r ? Finset.Icc 1 (N - 1), (-1) ^ r * (sigmaSum r : ?)

/-! ## Supporting lemma: |R_m| = ?(m) -/

/-- The set of divisor-row pairs: for each divisor `a` of `m`, we get rows `1..a`.
    This gives a bijection with `R m`. -/
private def divisorRows (m : ?) : Finset (? � ?) :=
  m.divisors.biUnion (fun a => (Finset.Icc 1 a).map ?fun i => (a, i), fun _ _ h => by
    exact Prod.ext_iff.mp h |>.2?)

/-- Supporting fact: `|R_m| = ?(m)` for every `m ? 1`.
    Proof strategy: Establish a bijection between R m and the set of pairs (a, i) where
    a | m and 1 ? i ? a. The cardinality of the latter is ?_{a | m} a = ?(m). -/
theorem card_R (m : ?) (hm : 1 ? m) : (R m).card = sigmaSum m := by
  -- Strategy: show R m bijects with ?_{a | m} Icc 1 a via the map (a,b,i) ? (a,i)
  -- since b is determined by a (b = m/a). Then |R m| = ?_{a | m} a = ?(m).
  have h_bij : (R m).card = ? a ? m.divisors, a := by
    have hm_ne : m ? 0 := by omega
    rw [show ? a ? m.divisors, a = ? a ? m.divisors, (Finset.Icc 1 a).card from by
      congr 1; ext a; simp [Nat.card_Icc]]
    rw [? Finset.card_sigma]
    apply Finset.card_bij (fun p _ => (?p.1, p.2.2? : (_ : ?) � ?))
    � -- maps into: (a, b, i) ? R m ? ?a, i? ? m.divisors.sigma (Icc 1)
      intro ?a, b, i? hmem
      simp only [R, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hmem
      simp only [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_Icc]
      obtain ???ha1, haM?, ?hb1, hbM?, hi1, hiM?, _, _, hab, _, hia? := hmem
      exact ???b, hab.symm?, hm_ne?, ?1 ? i?, hia?
    � -- injective
      intro ?a?, b?, i?? hmem? ?a?, b?, i?? hmem? heq
      simp only [R, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hmem? hmem?
      obtain ???ha?_1, _?, ?hb?_1, _?, _, _?, _, _, hab?, _, _? := hmem?
      obtain ???ha?_1, _?, ?hb?_1, _?, _, _?, _, _, hab?, _, _? := hmem?
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
      obtain ?ha_eq, hi_eq? := heq
      have hb_eq : b? = b? := by nlinarith
      ext <;> simp_all
    � -- surjective
      intro ?a, i? hmem
      simp only [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_Icc] at hmem
      obtain ??ha_dvd, _?, hi1, hi_le? := hmem
      have ha_pos : 0 < a := Nat.pos_of_ne_zero (fun h => by subst h; simp at ha_dvd; omega)
      set b := m / a with hb_def
      have hab : a * b = m := Nat.mul_div_cancel' ha_dvd
      have hb_pos : 0 < b := Nat.pos_of_ne_zero (fun h => by rw [h, Nat.mul_zero] at hab; omega)
      have ha_le_m : a ? m := Nat.le_of_dvd (by omega) ha_dvd
      have hb_le_m : b ? m := by nlinarith
      have hi_le_m : i ? m := by nlinarith [hi_le, ha_le_m]
      refine ?(a, b, i), ?_, rfl?
      simp only [R, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      exact ???by omega, ha_le_m?, ?by omega, hb_le_m?, by omega, hi_le_m?,
        by omega, by omega, hab, by omega, hi_le?
  -- sigmaSum m = ? d ? m.divisors, d by definition
  have h_sigma : sigmaSum m = ? a ? m.divisors, a := by
    rfl
  linarith

/-! ## Partition lemmas -/

/-- The positive and negative parts partition `X_N` (they are disjoint).
    Proof: a number cannot be both even and odd. Use Finset.disjoint_filter. -/
theorem disjoint_Xpos_Xneg (N : ?) : Disjoint (Xpos N) (Xneg N) := by
  apply Finset.disjoint_filter.mpr
  intro x _ heven hodd
  obtain ?k, hk? := heven
  obtain ?j, hj? := hodd
  omega

/-- The positive and negative parts cover `X_N`.
    Proof: every natural number is either even or odd. Use Finset.filter_union_filter_neg_eq. -/
theorem Xpos_union_Xneg (N : ?) : Xpos N ? Xneg N = X N := by
  unfold Xpos Xneg
  rw [? Finset.filter_or]
  apply Finset.filter_true_of_mem
  intro x _
  exact Nat.even_or_odd (x.1 * x.2.1)

/-! ## Lemma 1: q_n = |X_N^+| - |X_N^-| (signed count) -/

private lemma E_subset (N m : ?) : E N m ? {0, 1} := by
  unfold E; split_ifs <;> simp [Finset.subset_iff] <;> omega

/-- Helper: the number of elements of X_N with area exactly r equals
    |R_r| * |E_N(r)| = ?(r) * |E_N(r)|, which is 2*?(r) for r < N and ?(r) for r = N. -/
private lemma card_X_area_eq (N r : ?) (hr : 1 ? r) (hrN : r ? N) :
    ((X N).filter (fun p => p.1 * p.2.1 = r)).card =
      (R r).card * (E N r).card := by
  rw [? Finset.card_product]
  apply Finset.card_bij (fun p _ => ((p.1, p.2.1, p.2.2.1), p.2.2.2))
  � -- maps into
    intro ?a, b, i, ?? hmem
    simp only [Finset.mem_filter, X, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hmem
    obtain ????ha1, haN?, ?hb1, hbN?, ?hi1, hiN?, h?0, h?1?,
            ha_pos, hb_pos, hab_le, hi_pos, hi_le, hE_mem?, hab_eq? := hmem
    simp only [Finset.mem_product, R, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    have ha_le_r : a ? r := by nlinarith [Nat.le_mul_of_pos_left a (show 0 < b from by omega)]
    have hb_le_r : b ? r := by nlinarith [Nat.le_mul_of_pos_left b (show 0 < a from by omega)]
    have hi_le_r : i ? r := by nlinarith
    refine ????ha_pos, ha_le_r?, ?hb_pos, hb_le_r?, hi_pos, hi_le_r?,
            ha_pos, hb_pos, hab_eq, hi_pos, hi_le?, hab_eq ? hE_mem?
  � -- injective
    intro ?a?, b?, i?, ??? _ ?a?, b?, i?, ??? _ heq
    simp only [Prod.mk.injEq] at heq
    obtain ??ha, hb, hi?, h?? := heq
    exact Prod.ext ha (Prod.ext hb (Prod.ext hi h?))
  � -- surjective
    intro ??a, b, i?, ?? hmem
    simp only [Finset.mem_product, R, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hmem
    obtain ????ha1, har?, ?hb1, hbr?, hi1, hir?, ha_pos, hb_pos, hab_eq, hi_pos, hi_le?, h?_mem? := hmem
    refine ?(a, b, i, ?), ?_, rfl?
    simp only [Finset.mem_filter, X, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    have ha_le_N : a ? N := by nlinarith
    have hb_le_N : b ? N := by nlinarith [Nat.le_mul_of_pos_left b (show 0 < a from by omega)]
    have hi_le_N : i ? N := by nlinarith
    have h?_le_1 : ? ? 1 := by
      have hmem' := E_subset N r h?_mem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
      omega
    refine ????ha_pos, ha_le_N?, ?hb_pos, hb_le_N?, ?hi_pos, hi_le_N?, by omega, h?_le_1?,
            ha_pos, hb_pos, ?_, hi_pos, hi_le, ?_?, hab_eq?
    � rw [hab_eq]; exact hrN
    � rw [hab_eq]; exact h?_mem

/-- Helper: |E_N(r)| = 2 when r < N, and |E_N(N)| = 1. -/
private lemma card_E (N r : ?) (hr : 1 ? r) (hrN : r ? N) (hN : 2 ? N) :
    (E N r).card = if r < N then 2 else 1 := by
  unfold E
  split_ifs with h1 h2
  � simp
  � simp
  � omega

-- Combinatorial partition proof requires extra heartbeats for large sum manipulations
set_option maxHeartbeats 800000 in
/-- **Lemma 1 (signed count).** For every integer `n ? 1`, with `N = n + 1`,
`q_n = |X_N^+| - |X_N^-|` as an equality of integers.

Proof strategy: Decompose X_N by area value r from 1 to N. For each r:
- Elements with area r in X_N^+ exist iff r is even (contribute +|R_r|*|E_N(r)|)
- Elements with area r in X_N^- exist iff r is odd (contribute -|R_r|*|E_N(r)|)
Using card_R: |R_r| = ?(r), and card_E: |E_N(r)| = 2 for r < N, 1 for r = N.
So |X_N^+| - |X_N^-| = ?_{r even, r<N} 2?(r) + [?(N) if N even]
                      - ?_{r odd, r<N} 2?(r) - [?(N) if N odd]
                    = (-1)^N ?(N) + 2 ?_{r=1}^{N-1} (-1)^r ?(r) = q_n. -/
theorem q_signed_count (n : ?) (hn : 1 ? n) :
    qn n = ((Xpos (n + 1)).card : ?) - ((Xneg (n + 1)).card : ?) := by
  set N := n + 1
  -- Step 1: Express |Xpos N| as sum over even r of (card of elements with area r)
  have hXpos : ((Xpos N).card : ?) =
      ? r ? Finset.Icc 1 N, if Even r then
        ((R r).card * (E N r).card : ?) else 0 := by
    -- Partition Xpos by area value; use card_X_area_eq for each fiber
    have h_eq_biUnion : Xpos N =
        ((Finset.Icc 1 N).filter (fun r => Even r)).biUnion
          (fun r => (X N).filter (fun p => p.1 * p.2.1 = r)) := by
      ext p
      simp only [Xpos, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_Icc]
      constructor
      � intro ?hpX, heven?
        have hmem : p ? X N := hpX
        simp only [X, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hmem
        have hab_le : p.1 * p.2.1 ? N := hmem.2.2.2.1
        have hp1 : 1 ? p.1 := hmem.2.1
        have hp2 : 1 ? p.2.1 := hmem.2.2.1
        have h1 : 1 ? p.1 * p.2.1 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        exact ?p.1 * p.2.1, ??h1, hab_le?, heven?, hpX, rfl?
      � intro ?r, ?_, heven?, hpX, hr_eq?
        exact ?hpX, hr_eq ? heven?
    have h_disj : ? r ? (Finset.Icc 1 N).filter (fun r => Even r),
        ? s ? (Finset.Icc 1 N).filter (fun r => Even r), r ? s ?
        Disjoint ((X N).filter (fun p => p.1 * p.2.1 = r))
                 ((X N).filter (fun p => p.1 * p.2.1 = s)) := by
      intro r _ s _ hrs
      apply Finset.disjoint_filter.mpr
      intro p _ hr hs
      exact hrs (hr.symm ? hs)
    have h_card : (Xpos N).card =
        ? r ? (Finset.Icc 1 N).filter (fun r => Even r),
          ((X N).filter (fun p => p.1 * p.2.1 = r)).card := by
      rw [h_eq_biUnion]
      exact Finset.card_biUnion h_disj
    have h_subst : ? r ? (Finset.Icc 1 N).filter (fun r => Even r),
        ((X N).filter (fun p => p.1 * p.2.1 = r)).card =
        ? r ? (Finset.Icc 1 N).filter (fun r => Even r),
          (R r).card * (E N r).card := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_Icc] at hr
      exact card_X_area_eq N r hr.1.1 hr.1.2
    have h_filter_ite : ? r ? (Finset.Icc 1 N).filter (fun r => Even r),
        (R r).card * (E N r).card =
        ? r ? Finset.Icc 1 N, if Even r then (R r).card * (E N r).card else 0 := by
      rw [? Finset.sum_filter]
    have h_nat : (Xpos N).card =
        ? r ? Finset.Icc 1 N, if Even r then (R r).card * (E N r).card else 0 := by
      rw [h_card, h_subst, h_filter_ite]
    exact_mod_cast h_nat
  -- Step 2: Express |Xneg N| similarly for odd r
  have hXneg : ((Xneg N).card : ?) =
      ? r ? Finset.Icc 1 N, if Odd r then
        ((R r).card * (E N r).card : ?) else 0 := by
    have h_eq_biUnion : Xneg N =
        ((Finset.Icc 1 N).filter (fun r => Odd r)).biUnion
          (fun r => (X N).filter (fun p => p.1 * p.2.1 = r)) := by
      ext p
      simp only [Xneg, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_Icc]
      constructor
      � intro ?hpX, hodd?
        have hmem : p ? X N := hpX
        simp only [X, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hmem
        have hab_le : p.1 * p.2.1 ? N := hmem.2.2.2.1
        have hp1 : 1 ? p.1 := hmem.2.1
        have hp2 : 1 ? p.2.1 := hmem.2.2.1
        have h1 : 1 ? p.1 * p.2.1 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        exact ?p.1 * p.2.1, ??h1, hab_le?, hodd?, hpX, rfl?
      � intro ?r, ?_, hodd?, hpX, hr_eq?
        exact ?hpX, hr_eq ? hodd?
    have h_disj : ? r ? (Finset.Icc 1 N).filter (fun r => Odd r),
        ? s ? (Finset.Icc 1 N).filter (fun r => Odd r), r ? s ?
        Disjoint ((X N).filter (fun p => p.1 * p.2.1 = r))
                 ((X N).filter (fun p => p.1 * p.2.1 = s)) := by
      intro r _ s _ hrs
      apply Finset.disjoint_filter.mpr
      intro p _ hr hs
      exact hrs (hr.symm ? hs)
    have h_card : (Xneg N).card =
        ? r ? (Finset.Icc 1 N).filter (fun r => Odd r),
          ((X N).filter (fun p => p.1 * p.2.1 = r)).card := by
      rw [h_eq_biUnion]
      exact Finset.card_biUnion h_disj
    have h_subst : ? r ? (Finset.Icc 1 N).filter (fun r => Odd r),
        ((X N).filter (fun p => p.1 * p.2.1 = r)).card =
        ? r ? (Finset.Icc 1 N).filter (fun r => Odd r),
          (R r).card * (E N r).card := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_Icc] at hr
      exact card_X_area_eq N r hr.1.1 hr.1.2
    have h_filter_ite : ? r ? (Finset.Icc 1 N).filter (fun r => Odd r),
        (R r).card * (E N r).card =
        ? r ? Finset.Icc 1 N, if Odd r then (R r).card * (E N r).card else 0 := by
      rw [? Finset.sum_filter]
    have h_nat : (Xneg N).card =
        ? r ? Finset.Icc 1 N, if Odd r then (R r).card * (E N r).card else 0 := by
      rw [h_card, h_subst, h_filter_ite]
    exact_mod_cast h_nat
  -- Step 3: Compute the difference and match with qn definition
  -- |X^+| - |X^-| = ?_r (-1)^r * |R_r| * |E_N(r)| (signed sum)
  -- Using card_R (|R_r| = ?(r)) and card_E, this becomes exactly qn n.
  have hN : (2 : ?) ? N := by omega
  have h_diff : ((Xpos N).card : ?) - ((Xneg N).card : ?) =
      (-1 : ?) ^ N * (sigmaSum N : ?) +
      2 * ? r ? Finset.Icc 1 (N - 1), (-1 : ?) ^ r * (sigmaSum r : ?) := by
    -- Substitute hXpos, hXneg, use card_R and card_E to simplify each term.
    -- The r = N term gives (-1)^N * ?(N) (single color).
    -- The r < N terms give 2 * (-1)^r * ?(r) (double color).
    rw [hXpos, hXneg]
    push_cast
    rw [? Finset.sum_sub_distrib]
    -- Simplify each term: (if Even then X else 0) - (if Odd then X else 0) = (-1)^r * X
    have h_term : ? r ? Finset.Icc 1 N,
        (if Even r then ((R r).card * (E N r).card : ?) else 0) -
          (if Odd r then ((R r).card * (E N r).card : ?) else 0) =
        (-1 : ?) ^ r * ((R r).card * (E N r).card : ?) := by
      intro r hr
      rcases Nat.even_or_odd r with heven | hodd
      � have hnodd : � Odd r := by rwa [Nat.not_odd_iff_even]
        simp only [heven, ite_true, hnodd, ite_false, sub_zero]
        rw [heven.neg_one_pow, one_mul]
      � have hneven : � Even r := by rwa [Nat.not_even_iff_odd]
        simp only [hneven, ite_false, hodd, ite_true, zero_sub]
        rw [hodd.neg_one_pow]
        ring
    rw [Finset.sum_congr rfl h_term]
    -- Substitute card_R and card_E
    have h_subst : ? r ? Finset.Icc 1 N,
        (-1 : ?) ^ r * ((R r).card * (E N r).card : ?) =
        (-1 : ?) ^ r * (?(sigmaSum r) * ?(if r < N then 2 else 1 : ?)) := by
      intro r hr
      simp only [Finset.mem_Icc] at hr
      congr 1
      have h1 := card_R r hr.1
      have h2 := card_E N r hr.1 hr.2 hN
      push_cast [h1, h2]
      ring
    rw [Finset.sum_congr rfl h_subst]
    -- Split sum: Icc 1 N = Icc 1 (N-1) ? {N}
    have h_split : Finset.Icc 1 N = Finset.Icc 1 (N - 1) ? {N} := by
      ext x; simp [Finset.mem_Icc]; omega
    have h_disj : Disjoint (Finset.Icc 1 (N - 1)) ({N} : Finset ?) := by
      simp [Finset.disjoint_singleton_right, Finset.mem_Icc]; omega
    rw [h_split, Finset.sum_union h_disj, Finset.sum_singleton]
    -- Simplify the N term (r = N, so �(N < N))
    have h_N_simp : (-1 : ?) ^ N * (?(sigmaSum N) * ?(if N < N then 2 else 1 : ?)) =
        (-1 : ?) ^ N * ?(sigmaSum N) := by
      simp
    rw [h_N_simp]
    -- For r in Icc 1 (N-1), r < N so if gives 2
    have h_inner : ? r ? Finset.Icc 1 (N - 1),
        (-1 : ?) ^ r * (?(sigmaSum r) * ?(if r < N then 2 else 1 : ?)) =
        2 * ((-1 : ?) ^ r * ?(sigmaSum r)) := by
      intro r hr
      simp only [Finset.mem_Icc] at hr
      have hrN : r < N := by omega
      simp [hrN]; ring
    rw [Finset.sum_congr rfl h_inner, ? Finset.mul_sum]
    ring
  -- Step 4: The RHS of h_diff is exactly qn n by definition
  have h_qn_def : qn n = (-1 : ?) ^ N * (sigmaSum N : ?) +
      2 * ? r ? Finset.Icc 1 (N - 1), (-1 : ?) ^ r * (sigmaSum r : ?) := by
    rfl
  linarith

/-! ## Lemma 2: The injection X_N^- ? X_N^+ -/

/-- The explicit injection ? defined by cases on elements of X_N^-.
    Given (a, b, i, ?) ? X_N^- (so a*b is odd, hence a and b are both odd):
    - Case 1 (b > 1): ?(a,b,i,?) = (a, b-1, i, ?). Area a(b-1) is even, < ab ? N.
    - Case 2 (b = 1, a < N):
      - ? = 0: ?(a,1,i,0) = (a+1, 1, i, 0). Area a+1 is even.
      - ? = 1, i = 1: ?(a,1,1,1) = (a+1, 1, a+1, 0). Area a+1 is even.
      - ? = 1, i > 1: ?(a,1,i,1) = (a-1, 1, i-1, 1). Area a-1 is even (a odd, a?3).
    - Case 3 (b = 1, a = N, N odd):
      - i > 1: ?(N,1,i,0) = (N-1, 1, i-1, 1). Area N-1 is even.
      - i = 1: ?(N,1,1,0) = (1, N-1, 1, 1). Area N-1 is even.
-/
noncomputable def Phi (N : ?) (x : ? � ? � ? � ?) : ? � ? � ? � ? :=
  let a := x.1
  let b := x.2.1
  let i := x.2.2.1
  let ? := x.2.2.2
  if b > 1 then (a, b - 1, i, ?)  -- Case 1
  else if a < N then  -- Case 2 (b = 1, a < N)
    if ? = 0 then (a + 1, 1, i, 0)
    else if i = 1 then (a + 1, 1, a + 1, 0)
    else (a - 1, 1, i - 1, 1)
  else  -- Case 3 (b = 1, a = N)
    if i > 1 then (N - 1, 1, i - 1, 1)
    else (1, N - 1, 1, 1)

/-- Helper: Phi maps X_N^- into X_N^+. Each case produces an element with even area
    that satisfies all constraints of X_N. -/
private lemma Phi_maps_into (N : ?) (hN : 2 ? N) :
    ? x ? Xneg N, Phi N x ? Xpos N := by
  intro ?a, b, i, ?? hx
  simp only [Xneg, Finset.mem_filter] at hx
  obtain ?hxX, hodd? := hx
  simp only [X, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hxX
  obtain ???ha1, haN?, ?hb1, hbN?, ?hi1_icc, hiN?, h?0, h?1?, ha_pos, hb_pos, hab_le, hi_pos, hi_le, hE_mem? := hxX
  have ha_odd : Odd a := (Nat.odd_mul.mp hodd).1
  have hb_odd : Odd b := (Nat.odd_mul.mp hodd).2
  simp only [Xpos, Finset.mem_filter, X, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Phi]
  split_ifs with h1 h2 h3 h4 h5 <;> simp only [Prod.fst, Prod.snd]
  -- Case 1: b > 1
  � obtain ?kb, rfl? := hb_odd
    have hkb_pos : kb ? 1 := by omega
    have hbm1_eq : 2 * kb + 1 - 1 = 2 * kb := by omega
    rw [hbm1_eq]
    have h_area_lt : a * (2 * kb) < N := by nlinarith [Nat.mul_lt_mul_of_pos_left (show 2 * kb < 2 * kb + 1 from by omega) (show 0 < a from by omega)]
    refine ?????_, ?_?, ??_, ?_?, ??_, ?_?, ?_, ?_?, ?_, ?_, ?_, ?_, ?_, ?_?, ?_? <;> try omega
    � show ? ? E N (a * (2 * kb))
      rw [show E N (a * (2 * kb)) = {0, 1} from by unfold E; simp [h_area_lt]]
      simp only [E] at hE_mem
      split_ifs at hE_mem with h' <;> simp_all
    � exact ?a * kb, by ring?
  -- Case 2: �(b > 1), a < N, ? = 0
  � have hb_eq : b = 1 := by omega
    have ha1_even : Even (a + 1) := by obtain ?k, rfl? := ha_odd; exact ?k + 1, by omega?
    refine ?????_, ?_?, ??_, ?_?, ??_, ?_?, ?_, ?_?, ?_, ?_, ?_, ?_, ?_, ?_?, ?_? <;>
      first
        | omega
        | (simp only [Nat.mul_one, E]; split_ifs <;> simp_all <;> omega)
        | (simp only [Nat.mul_one]; exact ha1_even)
  -- Case 3: �(b > 1), a < N, ? ? 0, i = 1
  � have hb_eq : b = 1 := by omega
    have ha1_even : Even (a + 1) := by obtain ?k, rfl? := ha_odd; exact ?k + 1, by omega?
    refine ?????_, ?_?, ??_, ?_?, ??_, ?_?, ?_, ?_?, ?_, ?_, ?_, ?_, ?_, ?_?, ?_? <;>
      first
        | omega
        | (simp only [Nat.mul_one, E]; split_ifs <;> simp_all <;> omega)
        | (simp only [Nat.mul_one]; exact ha1_even)
  -- Case 4: �(b > 1), a < N, ? ? 0, i ? 1
  � have hb_eq : b = 1 := by omega
    have ha_ge3 : a ? 3 := by obtain ?k, rfl? := ha_odd; omega
    have ham1_even : Even (a - 1) := by obtain ?k, rfl? := ha_odd; exact ?k, by omega?
    refine ?????_, ?_?, ??_, ?_?, ??_, ?_?, ?_, ?_?, ?_, ?_, ?_, ?_, ?_, ?_?, ?_? <;>
      first
        | omega
        | (simp only [Nat.mul_one, E]; split_ifs <;> simp_all <;> omega)
        | (simp only [Nat.mul_one]; exact ham1_even)
  -- Case 5: �(b > 1), �(a < N), i > 1
  � have hb_eq : b = 1 := by omega
    have ha_eq : a = N := by omega
    have hN_odd : Odd N := by rw [? ha_eq]; exact ha_odd
    have hNm1_even : Even (N - 1) := by obtain ?k, rfl? := hN_odd; exact ?k, by omega?
    refine ?????_, ?_?, ??_, ?_?, ??_, ?_?, ?_, ?_?, ?_, ?_, ?_, ?_, ?_, ?_?, ?_? <;>
      first
        | omega
        | (simp only [Nat.mul_one, E]; split_ifs <;> simp_all <;> omega)
        | (simp only [Nat.mul_one]; exact hNm1_even)
  -- Case 6: �(b > 1), �(a < N), �(i > 1)
  � have hb_eq : b = 1 := by omega
    have ha_eq : a = N := by omega
    have hN_odd : Odd N := by rw [? ha_eq]; exact ha_odd
    have hNm1_even : Even (N - 1) := by obtain ?k, rfl? := hN_odd; exact ?k, by omega?
    refine ?????_, ?_?, ??_, ?_?, ??_, ?_?, ?_, ?_?, ?_, ?_, ?_, ?_, ?_, ?_?, ?_? <;>
      first
        | omega
        | (simp only [Nat.one_mul, E]; split_ifs <;> simp_all <;> omega)
        | (simp only [Nat.one_mul]; exact hNm1_even)

/-- Helper: Phi is injective on X_N^-. The proof proceeds by showing that different
    cases map to disjoint image sets (Case 1 images have b' ? 1 with b' even;
    Case 2/3 images have b' = 1 or b' = N-1) and within each case the map is injective
    (either by direct recovery of preimage coordinates, or by noting the map is
    strictly monotone on the relevant parameter). -/
private lemma E_eq_N' (N a b ? : ?) (hE : ? ? E N (a * b)) (hab : a * b = N) : ? = 0 := by
  unfold E at hE; simp [hab] at hE; exact hE

-- Injectivity proof requires many case splits from split_ifs (36 goals)
set_option maxHeartbeats 1600000 in
private lemma Phi_injOn (N : ?) (hN : 2 ? N) :
    Set.InjOn (Phi N) (Xneg N) := by
  intro ?a?, b?, i?, ??? hx? ?a?, b?, i?, ??? hx? heq
  rw [Finset.mem_coe] at hx? hx?
  simp only [Xneg, Finset.mem_filter, X, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc] at hx? hx?
  obtain ????ha?_lb, ha?_ub?, ?hb?_lb, hb?_ub?, ?hi?_lb_icc, hi?_ub_icc?,
    h??_lb, h??_ub?, ha?_pos, hb?_pos, hab?_le, hi?_pos, hi?_le, hE??, hodd?? := hx?
  obtain ????ha?_lb, ha?_ub?, ?hb?_lb, hb?_ub?, ?hi?_lb_icc, hi?_ub_icc?,
    h??_lb, h??_ub?, ha?_pos, hb?_pos, hab?_le, hi?_pos, hi?_le, hE??, hodd?? := hx?
  have ha?_odd : Odd a? := (Nat.odd_mul.mp hodd?).1
  have hb?_odd : Odd b? := (Nat.odd_mul.mp hodd?).2
  have ha?_odd : Odd a? := (Nat.odd_mul.mp hodd?).1
  have hb?_odd : Odd b? := (Nat.odd_mul.mp hodd?).2
  obtain ?k?, hk?? := ha?_odd
  obtain ?j?, hj?? := hb?_odd
  obtain ?k?, hk?? := ha?_odd
  obtain ?j?, hj?? := hb?_odd
  simp only [Phi] at heq
  split_ifs at heq with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  all_goals simp only [Prod.mk.injEq] at heq
  all_goals (try simp only [and_true, true_and] at heq)
  all_goals first
    | (exfalso; omega)
    | (obtain ?h_a, h_b, h_i, h_e? := heq; exfalso; omega)
    | (obtain ?h_a, h_b, h_i, h_e? := heq; simp only [Prod.mk.injEq]; omega)
    | (obtain ?h_a, h_i? := heq; simp only [Prod.mk.injEq]; omega)
    | (simp only [Prod.mk.injEq]; omega)
    -- E_eq_N' cases: b=1, a?N context ? a*b=N by omega after subst b=1
    | (obtain ?h_a, h_b, h_i, h_e? := heq; exfalso
       have hab? : a? * b? = N := by nlinarith [show b? = 1 from by omega]
       exact absurd (E_eq_N' N a? b? ?? hE? hab?) (by omega))
    | (obtain ?h_a, h_b, h_i, h_e? := heq; exfalso
       have hab? : a? * b? = N := by nlinarith [show b? = 1 from by omega]
       exact absurd (E_eq_N' N a? b? ?? hE? hab?) (by omega))
    -- E_eq_N' cases: a=1, b-1=N-1 ? b=N ? a*b=N
    | (obtain ?h_a, h_b, h_i, h_e? := heq; exfalso
       have hab? : a? * b? = N := by nlinarith [show a? = 1 from by omega, show b? = N from by omega]
       exact absurd (E_eq_N' N a? b? ?? hE? hab?) (by omega))
    | (obtain ?h_a, h_b, h_i, h_e? := heq; exfalso
       have hab? : a? * b? = N := by nlinarith [show a? = 1 from by omega, show b? = N from by omega]
       exact absurd (E_eq_N' N a? b? ?? hE? hab?) (by omega))
    -- Same-case equality with E_eq_N' (b=1, a?N for both)
    | (obtain ?h_i, _? := heq
       have hab? : a? * b? = N := by nlinarith [show b? = 1 from by omega]
       have hab? : a? * b? = N := by nlinarith [show b? = 1 from by omega]
       have := E_eq_N' N a? b? ?? hE? hab?
       have := E_eq_N' N a? b? ?? hE? hab?
       simp only [Prod.mk.injEq]; omega)
    | (have hab? : a? * b? = N := by nlinarith [show b? = 1 from by omega]
       have hab? : a? * b? = N := by nlinarith [show b? = 1 from by omega]
       have := E_eq_N' N a? b? ?? hE? hab?
       have := E_eq_N' N a? b? ?? hE? hab?
       simp only [Prod.mk.injEq]; omega)
    | (exfalso
       have hab? : a? * b? = N := by nlinarith [show b? = 1 from by omega]
       exact absurd (E_eq_N' N a? b? ?? hE? hab?) (by omega))
    | (exfalso
       have hab? : a? * b? = N := by nlinarith [show b? = 1 from by omega]
       exact absurd (E_eq_N' N a? b? ?? hE? hab?) (by omega))

/-- **Lemma 2 (injection).** For every integer `N ? 2` there exists a map
`? : X_N^- ? X_N^+` (modeled as a map on quadruples sending `X_N^-` into `X_N^+`)
that is injective on `X_N^-`. -/
theorem injection (N : ?) (hN : 2 ? N) :
    ? ? : (? � ? � ? � ?) ? (? � ? � ? � ?),
      (? x ? Xneg N, ? x ? Xpos N) ? Set.InjOn ? (Xneg N) := by
  exact ?Phi N, Phi_maps_into N hN, Phi_injOn N hN?

/-! ## Corollaries -/

/-- Consequence of Lemma 2: `|X_N^-| ? |X_N^+|`.
    Proof: use Finset.card_le_card_of_injOn with the injection from Lemma 2. -/
theorem card_Xneg_le_card_Xpos (N : ?) (hN : 2 ? N) :
    (Xneg N).card ? (Xpos N).card := by
  obtain ??, h?maps, h?inj? := injection N hN
  exact Finset.card_le_card_of_injOn ? h?maps h?inj

/-- **Corollary of Lemmas 1 and 2.** `q_n ? 0` for every integer `n ? 1`.
    Proof: By q_signed_count, qn n = |Xpos| - |Xneg|.
    By card_Xneg_le_card_Xpos, |Xneg| ? |Xpos|, so the difference is ? 0. -/
theorem qn_nonneg (n : ?) (hn : 1 ? n) : 0 ? qn n := by
  have hsigned := q_signed_count n hn
  have hcard := card_Xneg_le_card_Xpos (n + 1) (by omega : 2 ? n + 1)
  linarith [show ((Xneg (n + 1)).card : ?) ? ((Xpos (n + 1)).card : ?) from Nat.cast_le.mpr hcard]

end ColoredRectangles

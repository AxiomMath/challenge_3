import Mathlib

/-
# Problem Description

This problem concerns a divisor-sum quantity `q_n`, a combinatorial model of colored
marked rectangles, and a generating-function identity relating the inverse power series
`1 / S(t)` to a count of "assemblies".

Throughout, all "integer" variables ($a, b, i, m, n, N, r, \ell$) range over nonnegative
integers ($\mathbb{N}$), with positivity stated explicitly where required. We work over
$\mathbb{Z}$ for signed quantities and over $\mathbb{Q}$ for the power-series coefficients,
and use finite-set cardinalities (natural numbers) for the combinatorial counts.

## Background: provided building blocks

The following definitions and lemmas are described as *already provided and proven* in an
accompanying file. Definitions 1-7 are restated below for self-containedness, since the new
definitions and statements depend on them. The two provided lemmas are:

* Lemma 1 (`q_signed_count`): for $n \geq 1$, with $N = n + 1$, $q_n = |X_N^+| - |X_N^-|$.
* Lemma 2 (`injection`): for $N \geq 2$ there is an explicit map $\Phi_N$ sending $X_N^-$
  into $X_N^+$ and injective on $X_N^-$; with corollaries `card_Xneg_le_card_Xpos`
  ($|X_N^-| \leq |X_N^+|$) and `qn_nonneg` ($q_n \geq 0$).

These provided lemmas are stated below with their proofs left open, since they are not the
content of the task. The task is to formalize the two main statements (Proposition 1 and
Proposition 2).

## Main Definitions

* Definition 1 (`sigmaSum`): the divisor sum $\sigma(m) = \sum_{d \mid m} d$.
* Definition 2 (`qn`): with $N = n + 1$,
  $q_n = (-1)^N \sigma(N) + 2 \sum_{r=1}^{N-1} (-1)^r \sigma(r)$.
* Definition 3 (`R`): the rectangle set $R_m = \{ (a,b,i) : a,b \geq 1, ab = m, 1 \leq i \leq a \}$.
* Definition 4 (`E`): the color set $E_N(m)$ ($\{0,1\}$ for $m < N$, $\{0\}$ for $m = N$,
  $\varnothing$ otherwise).
* Definition 5 (`X`): the colored set $X_N$.
* Definition 6 (`Xpos`, `Xneg`): the positive/negative parts of $X_N$.
* Definition 7 (`Phi`): the explicit injection $\Phi_N$.
* Definition 8 (`Qset`): the unmatched set $Q_n = X_N^+ \setminus \Phi_N(X_N^-)$.
* Definition 9 (`Sps`, `cQ`): the power series $S(t) = \sum_{m \geq 0} \sigma(m+1)(-t)^m$
  and the coefficients $c_m$ of its multiplicative inverse $1/S(t)$.
* Definitions 10, 11 (`Passembly`, `Qwords`, `Wassembly`): the $P$-objects, the words of
  $Q$-blocks, and the assembly set $W_m$.

## Main Statements

* Proposition 1 (`prop_easy`): $(|Q_n| : \mathbb{Z}) = q_n$ for every $n \geq 1$.
* Proposition 2 (`prop_main`): $c_m = |W_m|$ for every $m \geq 0$; with the positivity
  consequence `cQ_pos`: $c_m > 0$.
-/

open Finset

namespace ColoredRectangles

/-! ## Provided definitions (Definitions 1-7) -/

/-- Definition 1: the divisor-sum function $\sigma(m) = \sum_{d \mid m} d$. -/
def sigmaSum (m : ℕ) : ℕ := ∑ d ∈ m.divisors, d

/-- Definition 3: the rectangle set $R_m$ as a finite set of triples $(a, b, i)$
with $a \cdot b = m$ and $1 \leq i \leq a$. -/
def R (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 m ×ˢ Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter
    (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2.1 ∧ p.1 * p.2.1 = m ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ p.1)

/-- Definition 4: the color set $E_N(m)$, equal to $\{0,1\}$ for $m < N$, $\{0\}$ for
$m = N$, and $\varnothing$ for $m > N$. -/
def E (N m : ℕ) : Finset ℕ := if m < N then {0, 1} else if m = N then {0} else ∅

/-- Definition 5: the colored set $X_N$ as a finite set of quadruples $(a, b, i, \varepsilon)$. -/
def X (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 0 1).filter
    (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2.1 ∧ p.1 * p.2.1 ≤ N ∧ 1 ≤ p.2.2.1 ∧ p.2.2.1 ≤ p.1 ∧
      p.2.2.2 ∈ E N (p.1 * p.2.1))

/-- Definition 6: the positive part $X_N^+$ (elements of even area). -/
def Xpos (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) := (X N).filter (fun p => Even (p.1 * p.2.1))

/-- Definition 6: the negative part $X_N^-$ (elements of odd area). -/
def Xneg (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) := (X N).filter (fun p => Odd (p.1 * p.2.1))

/-- Definition 2: the quantity $q_n$, with $N = n + 1$,
$q_n = (-1)^N \sigma(N) + 2 \sum_{r=1}^{N-1} (-1)^r \sigma(r)$. -/
def qn (n : ℕ) : ℤ :=
  let N := n + 1
  (-1) ^ N * (sigmaSum N : ℤ) + 2 * ∑ r ∈ Finset.Icc 1 (N - 1), (-1) ^ r * (sigmaSum r : ℤ)

/-- Definition 7: the explicit injection $\Phi$ defined by cases on elements of $X_N^-$.
Given $(a, b, i, \varepsilon) \in X_N^-$ (so $a \cdot b$ is odd, hence $a$ and $b$ are both odd):
- if $b > 1$: $\Phi(a,b,i,\varepsilon) = (a, b-1, i, \varepsilon)$;
- if $b = 1$, $a < N$, $\varepsilon = 0$: $\Phi(a,1,i,0) = (a+1, 1, i, 0)$;
- if $b = 1$, $a < N$, $\varepsilon = 1$, $i = 1$: $\Phi(a,1,1,1) = (a+1, 1, a+1, 0)$;
- if $b = 1$, $a < N$, $\varepsilon = 1$, $i > 1$: $\Phi(a,1,i,1) = (a-1, 1, i-1, 1)$;
- if $b = 1$, $a = N$, $i > 1$: $\Phi(N,1,i,0) = (N-1, 1, i-1, 1)$;
- if $b = 1$, $a = N$, $i = 1$: $\Phi(N,1,1,0) = (1, N-1, 1, 1)$. -/
noncomputable def Phi (N : ℕ) (x : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let a := x.1
  let b := x.2.1
  let i := x.2.2.1
  let ε := x.2.2.2
  if b > 1 then (a, b - 1, i, ε)
  else if a < N then
    if ε = 0 then (a + 1, 1, i, 0)
    else if i = 1 then (a + 1, 1, a + 1, 0)
    else (a - 1, 1, i - 1, 1)
  else
    if i > 1 then (N - 1, 1, i - 1, 1)
    else (1, N - 1, 1, 1)

/-! ## Provided lemmas (Lemmas 1 and 2 and corollaries)

These are described as supplied and proven in the accompanying file; here we record their
statements (with proofs left open) since the new statements depend on the surrounding
development. -/

/-- **Lemma 1 (signed count).** For every integer $n \geq 1$, with $N = n + 1$,
$q_n = |X_N^+| - |X_N^-|$ as an equality of integers. (Provided.) -/
theorem q_signed_count (n : ℕ) (hn : 1 ≤ n) :
    qn n = ((Xpos (n + 1)).card : ℤ) - ((Xneg (n + 1)).card : ℤ) := by
  sorry

/-- **Lemma 2 (injection).** For every integer $N \geq 2$ there exists a map
$\Phi : X_N^- \to X_N^+$ that is injective on $X_N^-$. (Provided; the explicit witness is
`Phi N`.) -/
theorem injection (N : ℕ) (hN : 2 ≤ N) :
    ∃ Φ : (ℕ × ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ × ℕ),
      (∀ x ∈ Xneg N, Φ x ∈ Xpos N) ∧ Set.InjOn Φ (Xneg N) := by
  sorry

/-- Consequence of Lemma 2: $|X_N^-| \leq |X_N^+|$. -/
theorem card_Xneg_le_card_Xpos (N : ℕ) (hN : 2 ≤ N) :
    (Xneg N).card ≤ (Xpos N).card := by
  obtain ⟨Φ, hΦmaps, hΦinj⟩ := injection N hN
  exact Finset.card_le_card_of_injOn Φ hΦmaps hΦinj

/-- **Corollary of Lemmas 1 and 2.** $q_n \geq 0$ for every integer $n \geq 1$. -/
theorem qn_nonneg (n : ℕ) (hn : 1 ≤ n) : 0 ≤ qn n := by
  have hsigned := q_signed_count n hn
  have hcard := card_Xneg_le_card_Xpos (n + 1) (by omega : 2 ≤ n + 1)
  linarith [show ((Xneg (n + 1)).card : ℤ) ≤ ((Xpos (n + 1)).card : ℤ) from Nat.cast_le.mpr hcard]

/-! ## New content: Definitions 8-11 and the two main propositions -/

/-- Definition 8: the unmatched set $Q_n = X_N^+ \setminus \Phi_N(X_N^-)$ (with $N = n + 1$),
modeled as a `Finset` difference. -/
noncomputable def Qset (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Xpos (n + 1)) \ ((Xneg (n + 1)).image (Phi (n + 1)))

/-- Definition 9: the power series $S(t) = \sum_{m \geq 0} \sigma(m+1)(-t)^m$, i.e. the
coefficient of $t^m$ is $(-1)^m \sigma(m+1)$. We work over $\mathbb{Q}$ so that $S$ has a
power-series inverse (its constant coefficient is $\sigma(1) = 1$, a unit). -/
noncomputable def Sps : PowerSeries ℚ :=
  PowerSeries.mk (fun m => (-1) ^ m * (sigmaSum (m + 1) : ℚ))

/-- Definition 9: the coefficients $c_m$ are the coefficients of the multiplicative
inverse $1 / S(t)$. -/
noncomputable def cQ (m : ℕ) : ℚ := PowerSeries.coeff (R := ℚ) m (Sps⁻¹)

/-- Correctness of Definition 9 (defining property): $S(t) \cdot (1/S(t)) = 1$ as power
series, which is exactly the Cauchy-product recurrence characterizing the $c_m$
($c_0 = 1$ and $\sum_{k=0}^m c_k (-1)^{m-k} \sigma(m-k+1) = 0$ for $m \geq 1$). -/
theorem Sps_mul_inv : Sps * Sps⁻¹ = 1 := by
  apply PowerSeries.mul_inv_cancel
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [Sps, sigmaSum]

/-- Definition 10: the $P$-objects $P_r$, a finite set of size $1$ (for $r = 0$) and $2$
(for $r \geq 1$). Concrete model: $P_0 = \{0\}$, $P_r = \{0, 1\}$ for $r \geq 1$. -/
def Passembly (r : ℕ) : Finset ℕ := Finset.range (if r = 0 then 1 else 2)

/-- Definition 11 (auxiliary): the set of words $[(n_1, A_1), \ldots, (n_\ell, A_\ell)]$ of
$Q$-blocks of total weight $w$, where each block records its weight $n_j \geq 1$ (stored as
$n_j$) and an element $A_j \in Q_{n_j}$. The order of the blocks matters (these are
words/ordered tuples). The empty word `[]` is the unique word of weight $0$. -/
noncomputable def Qwords : ℕ → Finset (List (ℕ × (ℕ × ℕ × ℕ × ℕ)))
  | 0 => {[]}
  | (w + 1) =>
      (Finset.range (w + 1)).biUnion (fun k =>
        (Qset (k + 1)).biUnion (fun A =>
          (Qwords (w - k)).image (fun l => (k + 1, A) :: l)))
  decreasing_by simp_wf

open Classical in
/-- Definition 11: the assembly set $W_m$. An assembly $(U; A_1, \ldots, A_\ell)$ is modeled
as $((r, U), \text{word})$, where $r \leq m$, $U \in P_r$ is a $P$-object, and word is a
$Q$-word of total weight $m - r$ (so the total weight $r + (n_1 + \cdots + n_\ell)$ is $m$). -/
noncomputable def Wassembly (m : ℕ) : Finset ((ℕ × ℕ) × List (ℕ × (ℕ × ℕ × ℕ × ℕ))) :=
  (Finset.range (m + 1)).biUnion (fun r =>
    (Passembly r).biUnion (fun U =>
      (Qwords (m - r)).image (fun w => ((r, U), w))))

/-- **Proposition 1 (`prop:easy`).** For every integer $n \geq 1$, the number of unmatched
positive colored marked rectangles equals $q_n$, as an equality of integers:
$(|Q_n| : \mathbb{Z}) = q_n$. -/
theorem prop_easy (n : ℕ) (hn : 1 ≤ n) : ((Qset n).card : ℤ) = qn n := by
  sorry

/-- **Proposition 2 (`prop:main`).** For every integer $m \geq 0$, the $m$-th coefficient
$c_m$ of $1/S(t)$ equals the number of assemblies $|W_m|$. -/
theorem prop_main (m : ℕ) : cQ m = ((Wassembly m).card : ℚ) := by
  sorry

/-- Positivity consequence of Proposition 2: $c_m > 0$ for every $m \geq 0$ (since $W_m$ is
nonempty). -/
theorem cQ_pos (m : ℕ) : 0 < cQ m := by
  sorry

end ColoredRectangles

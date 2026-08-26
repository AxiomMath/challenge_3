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
private def fiber' (N m : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (X N).filter (fun p => p.1 * p.2.1 = m)

private lemma fiber'_card (N m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) :
    (fiber' N m).card = sigmaSum m * (E N m).card := by
  suffices hbij : (fiber' N m).card = (R m ×ˢ E N m).card by
    rw [hbij, Finset.card_product]
    congr 1
    unfold sigmaSum
    conv_rhs => arg 2; ext d; rw [show d = (Finset.Icc 1 d).card from by simp [Nat.card_Icc]]
    rw [← Finset.card_sigma]
    apply Finset.card_bij (fun (p : ℕ × ℕ × ℕ) _ => (⟨p.1, p.2.2⟩ : (d : ℕ) × ℕ))
    · intro ⟨a, b, i⟩ hx
      simp only [R, mem_filter, mem_product, mem_Icc] at hx
      obtain ⟨⟨⟨ha1, ham⟩, ⟨hb1, hbm⟩, ⟨hi1, him⟩⟩, h1a, h1b, hab, h1i, hia⟩ := hx
      simp only [mem_sigma, Nat.mem_divisors, mem_Icc]
      exact ⟨⟨⟨b, hab.symm⟩, by omega⟩, h1i, hia⟩
    · intro a1 h1 a2 h2 heq
      simp only [R, mem_filter, mem_product, mem_Icc] at h1 h2
      have ha_eq : a1.1 = a2.1 := congr_arg Sigma.fst heq
      have hi_eq : a1.2.2 = a2.2.2 := eq_of_heq (Sigma.mk.inj heq).2
      have hab1 := h1.2.2.2.1
      have hab2 := h2.2.2.2.1
      have hb_eq : a1.2.1 = a2.2.1 := by nlinarith
      ext <;> [exact ha_eq; exact hb_eq; exact hi_eq]
    · intro ⟨d, i⟩ hx
      simp only [mem_sigma, Nat.mem_divisors, mem_Icc] at hx
      obtain ⟨⟨⟨b, hdb⟩, hm_ne⟩, h1i, hid⟩ := hx
      have hd_pos : 0 < d := by
        by_contra hd; push_neg at hd; interval_cases d; simp at hdb; omega
      have hb_pos : 0 < b := by
        by_contra hb; push_neg at hb; interval_cases b; simp at hdb; omega
      refine ⟨⟨d, b, i⟩, ?_, rfl⟩
      simp only [R, mem_filter, mem_product, mem_Icc]
      exact ⟨⟨⟨by omega, by nlinarith [hdb]⟩, ⟨by omega, by nlinarith [hdb]⟩, ⟨h1i, le_trans hid (by nlinarith [hdb])⟩⟩, by omega, by omega, hdb.symm, h1i, hid⟩
  apply Finset.card_bij (fun (x : ℕ × ℕ × ℕ × ℕ) _ => ((x.1, x.2.1, x.2.2.1), x.2.2.2))
  · intro ⟨a, b, i, ε⟩ hx
    simp only [fiber', X, E, R, mem_filter, mem_product, mem_Icc] at hx ⊢
    obtain ⟨⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩, ⟨hi1, hiN⟩, ⟨hε0, hε1⟩⟩, h1a, h1b, hab_le, h1i, hia, hε_mem⟩, hab_eq⟩ := hx
    refine ⟨⟨⟨⟨h1a, ?_⟩, ⟨h1b, ?_⟩, ⟨h1i, ?_⟩⟩, h1a, h1b, hab_eq, h1i, hia⟩, ?_⟩
    · nlinarith
    · nlinarith
    · nlinarith
    · rw [hab_eq] at hε_mem; exact hε_mem
  · intro a1 _ a2 _ heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := heq
    rcases a1 with ⟨a1₁, a1₂, a1₃, a1₄⟩
    rcases a2 with ⟨a2₁, a2₂, a2₃, a2₄⟩
    simp only at h1 h2 h3 h4
    subst h1; subst h2; subst h3; subst h4; rfl
  · intro ⟨⟨a, b, i⟩, ε⟩ hx
    simp only [R, E, mem_filter, mem_product, mem_Icc] at hx
    obtain ⟨⟨⟨⟨ha1, ham⟩, ⟨hb1, hbm⟩, ⟨hi1, him⟩⟩, h1a, h1b, hab_eq, h1i, hia⟩, hε_mem⟩ := hx
    have hε01 : ε = 0 ∨ ε = 1 := by
      split_ifs at hε_mem with h1 h2
      · simp [Finset.mem_insert, Finset.mem_singleton] at hε_mem; exact hε_mem
      · simp [Finset.mem_singleton] at hε_mem; left; exact hε_mem
      · exact absurd hε_mem (by simp)
    refine ⟨⟨a, b, i, ε⟩, ?_, rfl⟩
    simp only [fiber', X, E, mem_filter, mem_product, mem_Icc]
    refine ⟨⟨⟨⟨h1a, le_trans ham hmN⟩, ⟨h1b, le_trans hbm hmN⟩, ⟨h1i, le_trans him hmN⟩, ⟨by omega, by omega⟩⟩, h1a, h1b, ?_, h1i, hia, ?_⟩, hab_eq⟩
    · linarith [hab_eq ▸ hmN]
    · rw [hab_eq]; exact hε_mem

theorem q_signed_count (n : ℕ) (hn : 1 ≤ n) :
    qn n = ((Xpos (n + 1)).card : ℤ) - ((Xneg (n + 1)).card : ℤ) := by
  set N := n + 1 with hN_def
  suffices h : ((Xpos N).card : ℤ) - ((Xneg N).card : ℤ) =
      ∑ m ∈ Finset.Icc 1 N, (-1 : ℤ) ^ m * (sigmaSum m : ℤ) * ((E N m).card : ℤ) by
    have hqn : qn n = ∑ m ∈ Finset.Icc 1 N,
        (-1 : ℤ) ^ m * (sigmaSum m : ℤ) * ((E N m).card : ℤ) := by
      have hIcc : Finset.Icc 1 N = insert N (Finset.Icc 1 (N - 1)) := by
        ext m; simp [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp [Finset.mem_Icc]; omega)]
      have hEN : ((E N N).card : ℤ) = 1 := by simp [E]
      rw [hEN]
      have hrest : ∀ m ∈ Finset.Icc 1 (N - 1),
          (-1 : ℤ) ^ m * (sigmaSum m : ℤ) * ((E N m).card : ℤ) =
          2 * ((-1 : ℤ) ^ m * (sigmaSum m : ℤ)) := by
        intro m hm
        have hmN : m < N := by simp [Finset.mem_Icc] at hm; omega
        rw [show ((E N m).card : ℤ) = 2 from by exact_mod_cast (by simp [E, hmN] : (E N m).card = 2)]; ring
      rw [Finset.sum_congr rfl hrest, ← Finset.mul_sum]
      unfold qn; simp only [show n + 1 - 1 = n from by omega]
      rw [show N - 1 = n from by omega, hN_def,
          show ((-1 : ℤ) ^ (n + 1)) = -((-1 : ℤ) ^ n) from by ring_nf,
          show sigmaSum (n + 1) = sigmaSum N from by rw [hN_def]]
      ring
    linarith
  have hcard_diff : ((Xpos N).card : ℤ) - ((Xneg N).card : ℤ) =
      ∑ x ∈ X N, ((-1 : ℤ) ^ (x.1 * x.2.1)) := by
    have hpart : X N = Xpos N ∪ Xneg N := by
      ext x; simp only [Xpos, Xneg, mem_union, mem_filter]
      constructor
      · intro hx
        rcases Nat.even_or_odd (x.1 * x.2.1) with he | ho
        · left; exact ⟨hx, he⟩
        · right; exact ⟨hx, ho⟩
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    have hdisj : Disjoint (Xpos N) (Xneg N) := by
      simp only [Xpos, Xneg, disjoint_filter]
      exact fun x _ he ho => Nat.not_odd_iff_even.mpr he ho
    have hlhs : ((Xpos N).card : ℤ) - ((Xneg N).card : ℤ) =
        ∑ x ∈ Xpos N, (1 : ℤ) + ∑ x ∈ Xneg N, (-1 : ℤ) := by
      simp [Finset.sum_const]; ring
    have hrhs : ∑ x ∈ X N, ((-1 : ℤ) ^ (x.1 * x.2.1)) =
        ∑ x ∈ Xpos N, ((-1 : ℤ) ^ (x.1 * x.2.1)) + ∑ x ∈ Xneg N, ((-1 : ℤ) ^ (x.1 * x.2.1)) := by
      rw [hpart]; exact Finset.sum_union hdisj
    rw [hlhs, hrhs]; congr 1
    · apply Finset.sum_congr rfl
      intro x hx; simp only [Xpos, mem_filter] at hx
      obtain ⟨_, ⟨k, hk⟩⟩ := hx
      rw [hk, show k + k = 2 * k from by ring, pow_mul]; norm_num
    · apply Finset.sum_congr rfl
      intro x hx; simp only [Xneg, mem_filter] at hx
      obtain ⟨_, ⟨k, hk⟩⟩ := hx
      rw [hk, pow_add, pow_mul]; norm_num
  have hfib : ∑ x ∈ X N, ((-1 : ℤ) ^ (x.1 * x.2.1)) =
      ∑ m ∈ Finset.Icc 1 N, ∑ x ∈ fiber' N m, ((-1 : ℤ) ^ (x.1 * x.2.1)) := by
    have hmaps : ∀ x ∈ X N, x.1 * x.2.1 ∈ Finset.Icc 1 N := by
      intro x hx; simp only [X, mem_filter, mem_product, mem_Icc] at hx
      exact Finset.mem_Icc.mpr ⟨by nlinarith [hx.2.1, hx.2.2.1], hx.2.2.2.1⟩
    symm; exact Finset.sum_fiberwise_of_maps_to hmaps _
  have hinner : ∀ m ∈ Finset.Icc 1 N,
      ∑ x ∈ fiber' N m, ((-1 : ℤ) ^ (x.1 * x.2.1)) =
      (-1 : ℤ) ^ m * ((fiber' N m).card : ℤ) := by
    intro m _
    have h : ∀ x ∈ fiber' N m, ((-1 : ℤ) ^ (x.1 * x.2.1)) = (-1 : ℤ) ^ m := by
      intro x hx; simp only [fiber', mem_filter] at hx; rw [hx.2]
    rw [Finset.sum_congr rfl h, Finset.sum_const]; simp [mul_comm]
  have hfiber_eq : ∀ m ∈ Finset.Icc 1 N,
      (-1 : ℤ) ^ m * ((fiber' N m).card : ℤ) =
      (-1 : ℤ) ^ m * (sigmaSum m : ℤ) * ((E N m).card : ℤ) := by
    intro m hm
    have hm1 : 1 ≤ m := by simp [Finset.mem_Icc] at hm; omega
    have hmN1 : m ≤ N := by simp [Finset.mem_Icc] at hm; omega
    rw [fiber'_card N m hm1 hmN1]; push_cast; ring
  rw [hcard_diff, hfib, Finset.sum_congr rfl hinner, Finset.sum_congr rfl hfiber_eq]

private lemma odd_mul_odd_left {a b : ℕ} (h : Odd (a * b)) : Odd a := by
  rcases Nat.even_or_odd a with ⟨k, hk⟩ | ha
  · exfalso
    have hev : Even (a * b) := ⟨k * b, by subst hk; ring⟩
    exact Nat.not_odd_iff_even.mpr hev h
  · exact ha

private lemma odd_mul_odd_right {a b : ℕ} (h : Odd (a * b)) : Odd b := by
  rw [mul_comm] at h; exact odd_mul_odd_left h

private lemma odd_ge_3 {n : ℕ} (hn : Odd n) (h2 : n ≥ 2) : n ≥ 3 := by
  rcases hn with ⟨k, hk⟩; omega

private lemma Xneg_mem_data (N : ℕ) (x : ℕ × ℕ × ℕ × ℕ) (hx : x ∈ Xneg N) :
    1 ≤ x.1 ∧ x.1 ≤ N ∧ 1 ≤ x.2.1 ∧ x.2.1 ≤ N ∧ 1 ≤ x.2.2.1 ∧ x.2.2.1 ≤ x.1 ∧
    (x.2.2.2 = 0 ∨ x.2.2.2 = 1) ∧ x.1 * x.2.1 ≤ N ∧
    x.2.2.2 ∈ E N (x.1 * x.2.1) ∧ Odd (x.1 * x.2.1) := by
  simp only [Xneg, X, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
  refine ⟨hx.1.2.1, ?_, hx.1.2.2.1, ?_, hx.1.2.2.2.2.1, hx.1.2.2.2.2.2.1, ?_, hx.1.2.2.2.1, hx.1.2.2.2.2.2.2, hx.2⟩
  · have : x.1 ≤ x.1 * x.2.1 := Nat.le_mul_of_pos_right _ (by omega); omega
  · have : x.2.1 ≤ x.1 * x.2.1 := Nat.le_mul_of_pos_left _ (by omega); omega
  · have h01 := hx.1.1.2; omega

private lemma mem_Xpos' (N a b i ε : ℕ)
    (h1a : 1 ≤ a) (haN : a ≤ N) (h1b : 1 ≤ b) (hbN : b ≤ N)
    (h1i : 1 ≤ i) (hia : i ≤ a) (hab : a * b ≤ N)
    (heps : ε ∈ E N (a * b))
    (heven : Even (a * b)) : (a, b, i, ε) ∈ Xpos N := by
  simp only [Xpos, X, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨⟨⟨h1a, haN⟩, ⟨h1b, hbN⟩, ⟨h1i, le_trans hia haN⟩, ⟨Nat.zero_le _, ?_⟩⟩,
    h1a, h1b, hab, h1i, hia, heps⟩, heven⟩
  simp only [E] at heps
  split_ifs at heps <;> simp_all [Finset.mem_singleton, Finset.mem_insert] <;> omega

set_option maxHeartbeats 400000 in
/-- **Lemma 2 (injection).** For every integer $N \geq 2$ there exists a map
$\Phi : X_N^- \to X_N^+$ that is injective on $X_N^-$. (Provided; the explicit witness is
`Phi N`.) -/
theorem injection (N : ℕ) (hN : 2 ≤ N) :
    ∃ Φ : (ℕ × ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ × ℕ),
      (∀ x ∈ Xneg N, Φ x ∈ Xpos N) ∧ Set.InjOn Φ (Xneg N) := by
  refine ⟨Phi N, ?_, ?_⟩
  · -- Forward map
    intro x hx
    obtain ⟨h1a, haN', h1b, hbN, h1i, hia, heps01, hab, heps_E, hodd⟩ := Xneg_mem_data N x hx
    have ha_odd := odd_mul_odd_left hodd
    have hb_odd := odd_mul_odd_right hodd
    simp only [Phi]
    split_ifs with hb1 haN'' heps0 hi1 hi1'
    · -- Case 1: b > 1
      have hb3 : x.2.1 ≥ 3 := odd_ge_3 hb_odd (by omega)
      apply mem_Xpos'
      · exact h1a
      · exact haN'
      · omega
      · omega
      · exact h1i
      · exact hia
      · nlinarith [Nat.mul_lt_mul_of_pos_left (show x.2.1 - 1 < x.2.1 from by omega) (show 0 < x.1 from by omega)]
      · simp only [E]
        have hlt : x.1 * (x.2.1 - 1) < N := by nlinarith [Nat.mul_lt_mul_of_pos_left (show x.2.1 - 1 < x.2.1 from by omega) (show 0 < x.1 from by omega)]
        simp [hlt]; rcases heps01 with h | h <;> simp [h]
      · have : Even (x.2.1 - 1) := by rcases hb_odd with ⟨k, hk⟩; exact ⟨k, by omega⟩
        exact Even.mul_left this x.1
    · -- Case 2
      apply mem_Xpos'
      · omega
      · omega
      · omega
      · omega
      · exact h1i
      · omega
      · rw [Nat.mul_one]; omega
      · simp only [E, Nat.mul_one]
        rcases Nat.lt_or_eq_of_le (show x.1 + 1 ≤ N from by omega) with h | h
        · simp [h]
        · simp [show ¬ (x.1 + 1 < N) from by omega, h]
      · rw [Nat.mul_one]; rcases ha_odd with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
    · -- Case 3
      apply mem_Xpos'
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · rw [Nat.mul_one]; omega
      · simp only [E, Nat.mul_one]
        rcases Nat.lt_or_eq_of_le (show x.1 + 1 ≤ N from by omega) with h | h
        · simp [h]
        · simp [show ¬ (x.1 + 1 < N) from by omega, h]
      · rw [Nat.mul_one]; rcases ha_odd with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
    · -- Case 4
      have ha3 : x.1 ≥ 3 := odd_ge_3 ha_odd (by omega)
      apply mem_Xpos'
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · rw [Nat.mul_one]; omega
      · simp only [E, Nat.mul_one]; simp [show x.1 - 1 < N from by omega]
      · rw [Nat.mul_one]; rcases ha_odd with ⟨k, hk⟩; exact ⟨k, by omega⟩
    · -- Case 5
      have ha_eq : x.1 = N := by omega
      have hb1' : x.2.1 = 1 := by omega
      have hN_odd : Odd N := by
        have hab_eq : x.1 * x.2.1 = N := by rw [ha_eq, hb1', Nat.mul_one]
        rw [hab_eq] at hodd; exact hodd
      apply mem_Xpos'
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · rw [Nat.mul_one]; omega
      · simp only [E, Nat.mul_one]; simp [show N - 1 < N from by omega]
      · rw [Nat.mul_one]; rcases hN_odd with ⟨k, hk⟩; exact ⟨k, by omega⟩
    · -- Case 6
      have ha_eq : x.1 = N := by omega
      have hb1' : x.2.1 = 1 := by omega
      have hN_odd : Odd N := by
        have hab_eq : x.1 * x.2.1 = N := by rw [ha_eq, hb1', Nat.mul_one]
        rw [hab_eq] at hodd; exact hodd
      apply mem_Xpos'
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · rw [Nat.one_mul]; omega
      · simp only [E, Nat.one_mul]; simp [show N - 1 < N from by omega]
      · rw [Nat.one_mul]; rcases hN_odd with ⟨k, hk⟩; exact ⟨k, by omega⟩
  · -- Injectivity
    intro x hx y hy hxy
    obtain ⟨h1ax, haxN, h1bx, hbxN, h1ix, hiax, heps01x, habx, heps_Ex, hoddx⟩ := Xneg_mem_data N x hx
    obtain ⟨h1ay, hayN, h1by, hbyN, h1iy, hiay, heps01y, haby, heps_Ey, hoddy⟩ := Xneg_mem_data N y hy
    have hax_odd := odd_mul_odd_left hoddx
    have hbx_odd := odd_mul_odd_right hoddx
    have hay_odd := odd_mul_odd_left hoddy
    have hby_odd := odd_mul_odd_right hoddy
    have hepsx_aN : x.2.1 = 1 → x.1 = N → x.2.2.2 = 0 := by
      intro hb ha
      have hab_eq : x.1 * x.2.1 = N := by rw [ha, hb, Nat.mul_one]
      simp only [E, hab_eq, lt_irrefl, ↓reduceIte, Finset.mem_singleton] at heps_Ex; exact heps_Ex
    have hepsy_aN : y.2.1 = 1 → y.1 = N → y.2.2.2 = 0 := by
      intro hb ha
      have hab_eq : y.1 * y.2.1 = N := by rw [ha, hb, Nat.mul_one]
      simp only [E, hab_eq, lt_irrefl, ↓reduceIte, Finset.mem_singleton] at heps_Ey; exact heps_Ey
    simp only [Phi] at hxy
    split_ifs at hxy with hbx1 haxN' hεx0 hix1 hix1' hby1 hayN' hεy0 hiy1 hiy1'
    all_goals (simp only [Prod.mk.injEq] at hxy; obtain ⟨h_a, h_b, h_i, h_e⟩ := hxy)
    -- (1,1)
    · ext1 <;> [exact h_a; ext1 <;> [omega; ext1 <;> [exact h_i; exact h_e]]]
    -- (1,2)
    · exfalso; have := odd_ge_3 hbx_odd (by omega); omega
    -- (1,3)
    · exfalso; have := odd_ge_3 hbx_odd (by omega); omega
    -- (1,4)
    · exfalso; have := odd_ge_3 hbx_odd (by omega); omega
    -- (1,5)
    · exfalso; have := odd_ge_3 hbx_odd (by omega); omega
    -- (1,6)
    · have hx1 : x.1 = 1 := by omega
      have hxb : x.2.1 = N := by omega
      have : x.2.2.2 = 1 := by omega
      have hab_eq : x.1 * x.2.1 = N := by rw [hx1, hxb, Nat.one_mul]
      simp only [E, hab_eq, lt_irrefl, ↓reduceIte, Finset.mem_singleton] at heps_Ex; omega
    -- (2,1)
    · exfalso; have := odd_ge_3 hby_odd (by omega); omega
    -- (2,2)
    · have hbx1' : x.2.1 = 1 := by omega
      have hby1' : y.2.1 = 1 := by omega
      ext1 <;> [omega; ext1 <;> [omega; ext1 <;> [exact h_i; omega]]]
    -- (2,3)
    · exfalso; omega
    -- (2,4)
    · exfalso; omega
    -- (2,5)
    · exfalso; omega
    -- (2,6)
    · exfalso; omega
    -- (3,1)
    · exfalso; have := odd_ge_3 hby_odd (by omega); omega
    -- (3,2)
    · exfalso; omega
    -- (3,3)
    · have hbx1' : x.2.1 = 1 := by omega
      have hby1' : y.2.1 = 1 := by omega
      ext1 <;> [omega; ext1 <;> [omega; ext1 <;> omega]]
    -- (3,4)
    · exfalso; omega
    -- (3,5)
    · exfalso; omega
    -- (3,6)
    · exfalso; omega
    -- (4,1)
    · exfalso; have := odd_ge_3 hby_odd (by omega); omega
    -- (4,2)
    · exfalso; omega
    -- (4,3)
    · exfalso; omega
    -- (4,4)
    · have hbx1' : x.2.1 = 1 := by omega
      have hby1' : y.2.1 = 1 := by omega
      ext1 <;> [omega; ext1 <;> [omega; ext1 <;> omega]]
    -- (4,5)
    · exfalso; omega
    -- (4,6)
    · rcases hax_odd with ⟨k, hk⟩; omega
    -- (5,1)
    · exfalso; have := odd_ge_3 hby_odd (by omega); omega
    -- (5,2)
    · exfalso; omega
    -- (5,3)
    · exfalso; omega
    -- (5,4)
    · exfalso; omega
    -- (5,5)
    · have hbx1' : x.2.1 = 1 := by omega
      have hby1' : y.2.1 = 1 := by omega
      ext1 <;> [omega; ext1 <;> [omega; ext1 <;> omega]]
    -- (5,6)
    · have hbx1' : x.2.1 = 1 := by omega
      have hax_eq : x.1 = N := by omega
      have hN2 : N = 2 := by omega
      have hab_eq : x.1 * x.2.1 = 2 := by rw [hax_eq, hbx1', hN2, Nat.mul_one]
      rcases hoddx with ⟨k, hk⟩; omega
    -- (6,1)
    · have hy1 : y.1 = 1 := by omega
      have hyb : y.2.1 = N := by omega
      have : y.2.2.2 = 1 := by omega
      have hab_eq : y.1 * y.2.1 = N := by rw [hy1, hyb, Nat.one_mul]
      simp only [E, hab_eq, lt_irrefl, ↓reduceIte, Finset.mem_singleton] at heps_Ey; omega
    -- (6,2)
    · exfalso; omega
    -- (6,3)
    · exfalso; omega
    -- (6,4)
    · rcases hay_odd with ⟨k, hk⟩; omega
    -- (6,5)
    · have hbx1' : x.2.1 = 1 := by omega
      have hax_eq : x.1 = N := by omega
      have hN2 : N = 2 := by omega
      have hab_eq : x.1 * x.2.1 = 2 := by rw [hax_eq, hbx1', hN2, Nat.mul_one]
      rcases hoddx with ⟨k, hk⟩; omega
    -- (6,6)
    · have hbx1' : x.2.1 = 1 := by omega
      have hby1' : y.2.1 = 1 := by omega
      ext1 <;> [omega; ext1 <;> [omega; ext1 <;> omega]]

set_option maxHeartbeats 400000 in
/-- The forward map property of Phi: Phi N maps Xneg N into Xpos N.
    Extracted from the injection proof for direct use. -/
theorem Phi_maps_Xneg_to_Xpos (N : ℕ) (hN : 2 ≤ N) (x : ℕ × ℕ × ℕ × ℕ) (hx : x ∈ Xneg N) :
    Phi N x ∈ Xpos N := by
  obtain ⟨h1a, haN', h1b, hbN, h1i, hia, heps01, hab, heps_E, hodd⟩ := Xneg_mem_data N x hx
  have ha_odd := odd_mul_odd_left hodd
  have hb_odd := odd_mul_odd_right hodd
  simp only [Phi]
  split_ifs with hb1 haN'' heps0 hi1 hi1'
  · have hb3 : x.2.1 ≥ 3 := odd_ge_3 hb_odd (by omega)
    apply mem_Xpos'
    · exact h1a
    · exact haN'
    · omega
    · omega
    · exact h1i
    · exact hia
    · nlinarith [Nat.mul_lt_mul_of_pos_left (show x.2.1 - 1 < x.2.1 from by omega) (show 0 < x.1 from by omega)]
    · simp only [E]
      have hlt : x.1 * (x.2.1 - 1) < N := by nlinarith [Nat.mul_lt_mul_of_pos_left (show x.2.1 - 1 < x.2.1 from by omega) (show 0 < x.1 from by omega)]
      simp [hlt]; rcases heps01 with h | h <;> simp [h]
    · have : Even (x.2.1 - 1) := by rcases hb_odd with ⟨k, hk⟩; exact ⟨k, by omega⟩
      exact Even.mul_left this x.1
  · apply mem_Xpos'
    · omega
    · omega
    · omega
    · omega
    · exact h1i
    · omega
    · rw [Nat.mul_one]; omega
    · simp only [E, Nat.mul_one]
      rcases Nat.lt_or_eq_of_le (show x.1 + 1 ≤ N from by omega) with h | h
      · simp [h]
      · simp [show ¬ (x.1 + 1 < N) from by omega, h]
    · rw [Nat.mul_one]; rcases ha_odd with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
  · apply mem_Xpos'
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [Nat.mul_one]; omega
    · simp only [E, Nat.mul_one]
      rcases Nat.lt_or_eq_of_le (show x.1 + 1 ≤ N from by omega) with h | h
      · simp [h]
      · simp [show ¬ (x.1 + 1 < N) from by omega, h]
    · rw [Nat.mul_one]; rcases ha_odd with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
  · have ha3 : x.1 ≥ 3 := odd_ge_3 ha_odd (by omega)
    apply mem_Xpos'
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [Nat.mul_one]; omega
    · simp only [E, Nat.mul_one]; simp [show x.1 - 1 < N from by omega]
    · rw [Nat.mul_one]; rcases ha_odd with ⟨k, hk⟩; exact ⟨k, by omega⟩
  · have ha_eq : x.1 = N := by omega
    have hb1' : x.2.1 = 1 := by omega
    have hN_odd : Odd N := by
      have hab_eq : x.1 * x.2.1 = N := by rw [ha_eq, hb1', Nat.mul_one]
      rw [hab_eq] at hodd; exact hodd
    apply mem_Xpos'
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [Nat.mul_one]; omega
    · simp only [E, Nat.mul_one]; simp [show N - 1 < N from by omega]
    · rw [Nat.mul_one]; rcases hN_odd with ⟨k, hk⟩; exact ⟨k, by omega⟩
  · have ha_eq : x.1 = N := by omega
    have hb1' : x.2.1 = 1 := by omega
    have hN_odd : Odd N := by
      have hab_eq : x.1 * x.2.1 = N := by rw [ha_eq, hb1', Nat.mul_one]
      rw [hab_eq] at hodd; exact hodd
    apply mem_Xpos'
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [Nat.one_mul]; omega
    · simp only [E, Nat.one_mul]; simp [show N - 1 < N from by omega]
    · rw [Nat.one_mul]; rcases hN_odd with ⟨k, hk⟩; exact ⟨k, by omega⟩

set_option maxHeartbeats 400000 in
/-- The injectivity property of Phi on Xneg.
    Extracted from the injection proof for direct use. -/
theorem Phi_injOn_Xneg (N : ℕ) (hN : 2 ≤ N) : Set.InjOn (Phi N) (Xneg N) := by
  intro x hx y hy hxy
  obtain ⟨h1ax, haxN, h1bx, hbxN, h1ix, hiax, heps01x, habx, heps_Ex, hoddx⟩ := Xneg_mem_data N x hx
  obtain ⟨h1ay, hayN, h1by, hbyN, h1iy, hiay, heps01y, haby, heps_Ey, hoddy⟩ := Xneg_mem_data N y hy
  have hax_odd := odd_mul_odd_left hoddx
  have hbx_odd := odd_mul_odd_right hoddx
  have hay_odd := odd_mul_odd_left hoddy
  have hby_odd := odd_mul_odd_right hoddy
  have hepsx_aN : x.2.1 = 1 → x.1 = N → x.2.2.2 = 0 := by
    intro hb ha
    have hab_eq : x.1 * x.2.1 = N := by rw [ha, hb, Nat.mul_one]
    simp only [E, hab_eq, lt_irrefl, ↓reduceIte, Finset.mem_singleton] at heps_Ex; exact heps_Ex
  have hepsy_aN : y.2.1 = 1 → y.1 = N → y.2.2.2 = 0 := by
    intro hb ha
    have hab_eq : y.1 * y.2.1 = N := by rw [ha, hb, Nat.mul_one]
    simp only [E, hab_eq, lt_irrefl, ↓reduceIte, Finset.mem_singleton] at heps_Ey; exact heps_Ey
  simp only [Phi] at hxy
  split_ifs at hxy with hbx1 haxN' hεx0 hix1 hix1' hby1 hayN' hεy0 hiy1 hiy1'
  all_goals (simp only [Prod.mk.injEq] at hxy; obtain ⟨h_a, h_b, h_i, h_e⟩ := hxy)
  · ext1 <;> [exact h_a; ext1 <;> [omega; ext1 <;> [exact h_i; exact h_e]]]
  · exfalso; have := odd_ge_3 hbx_odd (by omega); omega
  · exfalso; have := odd_ge_3 hbx_odd (by omega); omega
  · exfalso; have := odd_ge_3 hbx_odd (by omega); omega
  · exfalso; have := odd_ge_3 hbx_odd (by omega); omega
  · have hx1 : x.1 = 1 := by omega
    have hxb : x.2.1 = N := by omega
    have : x.2.2.2 = 1 := by omega
    have hab_eq : x.1 * x.2.1 = N := by rw [hx1, hxb, Nat.one_mul]
    simp only [E, hab_eq, lt_irrefl, ↓reduceIte, Finset.mem_singleton] at heps_Ex; omega
  · exfalso; have := odd_ge_3 hby_odd (by omega); omega
  · have hbx1' : x.2.1 = 1 := by omega
    have hby1' : y.2.1 = 1 := by omega
    ext1 <;> [omega; ext1 <;> [omega; ext1 <;> [exact h_i; omega]]]
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; have := odd_ge_3 hby_odd (by omega); omega
  · exfalso; omega
  · have hbx1' : x.2.1 = 1 := by omega
    have hby1' : y.2.1 = 1 := by omega
    ext1 <;> [omega; ext1 <;> [omega; ext1 <;> omega]]
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; have := odd_ge_3 hby_odd (by omega); omega
  · exfalso; omega
  · exfalso; omega
  · have hbx1' : x.2.1 = 1 := by omega
    have hby1' : y.2.1 = 1 := by omega
    ext1 <;> [omega; ext1 <;> [omega; ext1 <;> omega]]
  · exfalso; omega
  · rcases hax_odd with ⟨k, hk⟩; omega
  · exfalso; have := odd_ge_3 hby_odd (by omega); omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · have hbx1' : x.2.1 = 1 := by omega
    have hby1' : y.2.1 = 1 := by omega
    ext1 <;> [omega; ext1 <;> [omega; ext1 <;> omega]]
  · have hbx1' : x.2.1 = 1 := by omega
    have hax_eq : x.1 = N := by omega
    have hN2 : N = 2 := by omega
    have hab_eq : x.1 * x.2.1 = 2 := by rw [hax_eq, hbx1', hN2, Nat.mul_one]
    rcases hoddx with ⟨k, hk⟩; omega
  · have hy1 : y.1 = 1 := by omega
    have hyb : y.2.1 = N := by omega
    have : y.2.2.2 = 1 := by omega
    have hab_eq : y.1 * y.2.1 = N := by rw [hy1, hyb, Nat.one_mul]
    simp only [E, hab_eq, lt_irrefl, ↓reduceIte, Finset.mem_singleton] at heps_Ey; omega
  · exfalso; omega
  · exfalso; omega
  · rcases hay_odd with ⟨k, hk⟩; omega
  · have hbx1' : x.2.1 = 1 := by omega
    have hax_eq : x.1 = N := by omega
    have hN2 : N = 2 := by omega
    have hab_eq : x.1 * x.2.1 = 2 := by rw [hax_eq, hbx1', hN2, Nat.mul_one]
    rcases hoddx with ⟨k, hk⟩; omega
  · have hbx1' : x.2.1 = 1 := by omega
    have hby1' : y.2.1 = 1 := by omega
    ext1 <;> [omega; ext1 <;> [omega; ext1 <;> omega]]

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

/-! ### Helper lemmas for Proposition 1 -/

/-- The image of Phi on Xneg is a subset of Xpos.
    Proof strategy: The `injection` theorem provides a witness Φ with ∀ x ∈ Xneg N, Φ x ∈ Xpos N.
    We need to show that `Phi N` specifically has this property. Since `injection` is existential
    and its witness is `Phi N`, we need to show Phi N maps Xneg into Xpos. This follows from the
    definition of Phi and membership conditions. Use `Finset.image_subset_iff`. -/
theorem Phi_image_subset_Xpos (N : ℕ) (hN : 2 ≤ N) :
    (Xneg N).image (Phi N) ⊆ Xpos N := by
  rw [Finset.image_subset_iff]
  intro x hx
  exact Phi_maps_Xneg_to_Xpos N hN x hx

/-- Phi is injective on Xneg, so the image has the same cardinality.
    Proof strategy: Use `Finset.card_image_of_injOn`. The `injection` theorem provides
    Set.InjOn for the witness Phi N on Xneg N. Apply card_image_of_injOn directly. -/
theorem card_Phi_image (N : ℕ) (hN : 2 ≤ N) :
    ((Xneg N).image (Phi N)).card = (Xneg N).card := by
  exact Finset.card_image_of_injOn (Phi_injOn_Xneg N hN)

/-- **Proposition 1 (`prop:easy`).** For every integer $n \geq 1$, the number of unmatched
positive colored marked rectangles equals $q_n$, as an equality of integers:
$(|Q_n| : \mathbb{Z}) = q_n$. -/
theorem prop_easy (n : ℕ) (hn : 1 ≤ n) : ((Qset n).card : ℤ) = qn n := by
  -- Proof: Qset n = Xpos(n+1) \ image(Phi(n+1), Xneg(n+1))
  -- Since image ⊆ Xpos (by Phi_image_subset_Xpos), Finset.card_sdiff_of_subset applies:
  --   card(Qset n) = card(Xpos) - card(image)
  -- Since Phi is injective (by card_Phi_image): card(image) = card(Xneg)
  -- Therefore: card(Qset n) = card(Xpos) - card(Xneg)
  -- By q_signed_count: qn n = card(Xpos) - card(Xneg) as integers
  -- The cast and omega close the gap.
  have hN : 2 ≤ n + 1 := by omega
  have hsub : (Xneg (n + 1)).image (Phi (n + 1)) ⊆ Xpos (n + 1) := Phi_image_subset_Xpos (n + 1) hN
  have hcard_img : ((Xneg (n + 1)).image (Phi (n + 1))).card = (Xneg (n + 1)).card :=
    card_Phi_image (n + 1) hN
  have hsdiff : (Qset n).card = (Xpos (n + 1)).card - (Xneg (n + 1)).card := by
    unfold Qset
    rw [Finset.card_sdiff_of_subset hsub, hcard_img]
  rw [q_signed_count n hn]
  have hle := card_Xneg_le_card_Xpos (n + 1) hN
  omega

/-! ### Helper lemmas for Proposition 2 -/

/-- The P-generating function as a power series: P(t) = mk (fun r => |P_r|) = 1 + 2t + 2t² + ...
    We define Pps as the formal power series with coefficient 1 at index 0, and 2 at index r ≥ 1. -/
noncomputable def Pps : PowerSeries ℚ :=
  PowerSeries.mk (fun r => if r = 0 then (1 : ℚ) else 2)

/-- The Q-generating function: Q(t) = Σ_{n≥1} q_n · t^n (with Q(0) = 0). -/
noncomputable def Qps : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (qn n : ℚ))

/-- Key identity: P(t) · S(t) + Q(t) = 1, equivalently Q(t) = 1 - P(t)·S(t).
    Proof strategy: Compare coefficients on both sides. The constant term of P·S is
    |P_0|·σ(1)·(-1)^0 = 1·1·1 = 1, and Q(0) = 0, so the constant term of P·S + Q is 1.
    For m ≥ 1, [t^m](P·S) = Σ_{r=0}^m |P_r|·(-1)^{m-r}·σ(m-r+1)
      = (-1)^m·σ(m+1) + 2·Σ_{r=1}^m (-1)^{m-r}·σ(m-r+1).
    By a change of index j = m - r, this equals
      (-1)^m·σ(m+1) + 2·Σ_{j=0}^{m-1} (-1)^j·σ(j+1).
    Meanwhile, qn(m) = (-1)^{m+1}·σ(m+1) + 2·Σ_{r=1}^m (-1)^r·σ(r)
      = -(-1)^m·σ(m+1) + 2·Σ_{j=1}^m (-1)^j·σ(j).
    So [t^m](P·S) + qn(m) = (-1)^m·σ(m+1) - (-1)^m·σ(m+1) + 2·Σ_{j=0}^{m-1}(-1)^j·σ(j+1)
      + 2·Σ_{j=1}^m (-1)^j·σ(j).
    The sums Σ_{j=0}^{m-1}(-1)^j·σ(j+1) and Σ_{j=1}^m (-1)^j·σ(j) are equal (re-index k=j+1),
    so [t^m](P·S) + qn(m) = 2·(sum) + 2·(sum) ... Actually let's be more careful:
    The key observation is [t^m](P·S) = -qn(m) for m ≥ 1, giving P·S + Q = 1. -/
theorem PS_plus_Q_eq_one : Pps * Sps + Qps = 1 := by
  have sums_cancel : ∀ m : ℕ,
      ∑ x ∈ Finset.range m, (sigmaSum (1 + (m - (1 + x))) : ℚ) * (-1 : ℚ) ^ (m - (1 + x)) =
      -(∑ x ∈ Finset.Icc 1 m, (sigmaSum x : ℚ) * (-1 : ℚ) ^ x) := by
    intro m
    have h_eq : ∑ x ∈ Finset.range m, (sigmaSum (1 + (m - (1 + x))) : ℚ) * (-1 : ℚ) ^ (m - (1 + x)) =
      ∑ r ∈ Finset.Icc 1 m, (sigmaSum r : ℚ) * (-1 : ℚ) ^ (r - 1) := by
      apply Finset.sum_bij' (fun x _ => m - x) (fun r _ => m - r)
      · intro x hx
        have hx' := Finset.mem_range.mp hx
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro r hr
        have hr' := Finset.mem_Icc.mp hr
        exact Finset.mem_range.mpr (by omega)
      · intro x hx; have := Finset.mem_range.mp hx; omega
      · intro r hr; have := Finset.mem_Icc.mp hr; omega
      · intro x hx
        have hx' := Finset.mem_range.mp hx
        have h1 : 1 + (m - (1 + x)) = m - x := by omega
        have h2 : m - (1 + x) = (m - x) - 1 := by omega
        rw [h1, h2]
    rw [h_eq, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' := Finset.mem_Icc.mp hr
    have hpow : ((-1 : ℚ) ^ (r - 1)) = -((-1 : ℚ) ^ r) := by
      have h : r = r - 1 + 1 := by omega
      conv_rhs => rw [h, pow_succ]; ring
    rw [hpow]; ring
  ext m
  simp only [map_add, PowerSeries.coeff_one]
  rw [PowerSeries.coeff_mul]
  simp only [Pps, Sps, Qps, PowerSeries.coeff_mk]
  by_cases hm : m = 0
  · subst hm; simp [Finset.antidiagonal_zero, sigmaSum]
  · simp only [hm, ↓reduceIte]
    -- Need to show: Cauchy product sum + qn m = 0
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
    conv_lhs =>
      arg 1
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => (if i = 0 then (1:ℚ) else 2) * ((-1) ^ j * (sigmaSum (j + 1) : ℚ)))]
    rw [Finset.sum_range_succ'
      (fun k => (if k = 0 then (1:ℚ) else 2) * ((-1) ^ (m - k) * (sigmaSum (m - k + 1) : ℚ)))]
    simp only [Nat.sub_zero, ↓reduceIte]
    have hsimp : ∀ k ∈ Finset.range m,
      (if k + 1 = 0 then (1:ℚ) else 2) * ((-1) ^ (m - (k + 1)) * (sigmaSum (m - (k + 1) + 1) : ℚ)) =
      2 * ((-1) ^ (m - (k + 1)) * (sigmaSum (m - (k + 1) + 1) : ℚ)) := by
      intro k _; simp
    rw [Finset.sum_congr rfl hsimp]
    unfold qn
    simp only [show m + 1 - 1 = m from by omega]
    push_cast
    ring_nf
    conv_lhs =>
      arg 1
      rw [show (∑ x ∈ Finset.range m,
        (sigmaSum (1 + (m - (1 + x))) : ℚ) * (-1 : ℚ) ^ (m - (1 + x)) * 2) =
        (∑ x ∈ Finset.range m, (sigmaSum (1 + (m - (1 + x))) : ℚ) * (-1 : ℚ) ^ (m - (1 + x))) * 2
        from (Finset.sum_mul ..).symm]
    linarith [sums_cancel m]

/-- The generating function of |W_m| equals P(t) · (geometric series in Q(t)).
    Specifically: |W_m| = Σ_{r+w=m} |P_r| · |Qwords(w)| where |Qwords(w)| is the
    number of Q-words of total weight w. The generating function of |Qwords(w)| is
    1/(1-Q(t)) (geometric series, valid because Q(0) = 0). So the generating function
    of |W_m| is P(t) · 1/(1-Q(t)).

    Proof strategy: By definition, Wassembly(m) = ∪_{r≤m} P_r × Qwords(m-r) (as sets),
    where elements are injectively represented via the image construction.
    Therefore |W_m| = Σ_{r=0}^m |P_r| · |Qwords(m-r)|.
    This means the GF of |W_m| = Pps · (GF of |Qwords|).
    For |Qwords|: by definition of Qwords, the GF of |Qwords(w)| satisfies the
    geometric series recurrence (since Qwords decomposes as a word with first block
    of weight n ≥ 1 from Q_n followed by a word of weight w-n). So GF of Qwords = 1/(1-Qps).
    Overall: GF of |W_m| = Pps / (1 - Qps). -/
private lemma Qset_card_cast' (n : ℕ) (hn : 1 ≤ n) : ((Qset n).card : ℚ) = (qn n : ℚ) := by
  have h := prop_easy n hn; exact_mod_cast h

open Classical in
private lemma Qwords_card_succ_cast' (w : ℕ) :
    ((Qwords (w + 1)).card : ℚ) = ∑ k ∈ Finset.range (w + 1),
      (qn (k + 1) : ℚ) * ((Qwords (w - k)).card : ℚ) := by
  have hcard : (Qwords (w + 1)).card = ∑ k ∈ Finset.range (w + 1),
      (Qset (k + 1)).card * (Qwords (w - k)).card := by
    rw [Qwords]
    rw [Finset.card_biUnion]
    · congr 1; ext k
      rw [Finset.card_biUnion]
      · simp only [Finset.card_image_of_injective _ (List.cons_injective)]
        exact Finset.sum_const _
      · intro A _ B _ hAB
        simp only [Finset.disjoint_left, Finset.mem_image]
        intro x ⟨l1, _, hl1⟩ ⟨l2, _, hl2⟩
        rw [← hl1] at hl2
        exact hAB ((Prod.mk.inj (List.cons.inj hl2).1).2.symm)
    · intro i _ j _ hij
      simp only [Finset.disjoint_left, Finset.mem_biUnion, Finset.mem_image]
      intro x ⟨A, _, l1, _, hl1⟩ ⟨B, _, l2, _, hl2⟩
      rw [← hl1] at hl2
      have heq := (Prod.mk.inj (List.cons.inj hl2).1).1
      exact hij (by omega : i = j)
  have hc : ((Qwords (w + 1)).card : ℚ) =
      ∑ k ∈ Finset.range (w + 1), ((Qset (k + 1)).card : ℚ) * ((Qwords (w - k)).card : ℚ) := by
    rw [hcard]; push_cast; ring_nf
  rw [hc]
  exact Finset.sum_congr rfl (fun k _ => by rw [Qset_card_cast' (k + 1) (by omega)])

open Classical in
private lemma Wassembly_card_eq' (m : ℕ) :
    ((Wassembly m).card : ℚ) = ∑ r ∈ Finset.range (m + 1),
      ((Passembly r).card : ℚ) * ((Qwords (m - r)).card : ℚ) := by
  have hcard : (Wassembly m).card = ∑ r ∈ Finset.range (m + 1),
      (Passembly r).card * (Qwords (m - r)).card := by
    rw [Wassembly]
    rw [Finset.card_biUnion]
    · congr 1; ext r
      rw [Finset.card_biUnion]
      · have : ∀ u ∈ Passembly r,
            (Finset.image (fun w => ((r, u), w)) (Qwords (m - r))).card = (Qwords (m - r)).card := by
          intro u _
          exact Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)
        rw [Finset.sum_congr rfl (fun u hu => this u hu)]
        exact Finset.sum_const _
      · intro U _ V _ hUV
        simp only [Finset.disjoint_left, Finset.mem_image]
        intro x ⟨w1, _, hw1⟩ ⟨w2, _, hw2⟩
        rw [← hw1] at hw2
        exact hUV ((Prod.mk.inj (Prod.mk.inj hw2).1).2.symm)
    · intro i _ j _ hij
      simp only [Finset.disjoint_left, Finset.mem_biUnion, Finset.mem_image]
      intro x ⟨U, _, w1, _, hw1⟩ ⟨V, _, w2, _, hw2⟩
      rw [← hw1] at hw2
      exact hij ((Prod.mk.inj (Prod.mk.inj hw2).1).1.symm)
  rw [hcard]; push_cast; ring_nf

theorem Wassembly_gf_eq_P_div_one_minus_Q :
    PowerSeries.mk (fun m => ((Wassembly m).card : ℚ)) = Pps * (1 - Qps)⁻¹ := by
  set QGF := PowerSeries.mk (fun w => ((Qwords w).card : ℚ)) with hQGF_def
  -- Step 1: (1-Qps) * QGF = 1
  have h_inv : (1 - Qps) * QGF = 1 := by
    ext m
    rw [PowerSeries.coeff_one,
        show (PowerSeries.coeff m) ((1 - Qps) * QGF) =
          ∑ ij ∈ Finset.antidiagonal m,
            ((PowerSeries.coeff ij.1) (1 - Qps)) * ((PowerSeries.coeff ij.2) QGF)
          from PowerSeries.coeff_mul m (1 - Qps) QGF]
    simp only [hQGF_def, Qps, PowerSeries.coeff_mk, map_sub, PowerSeries.coeff_one]
    have hcoeff : ∀ ij ∈ Finset.antidiagonal m,
        ((if ij.1 = 0 then (1 : ℚ) else 0) - (if ij.1 = 0 then (0 : ℚ) else (qn ij.1 : ℚ))) *
          ((Qwords ij.2).card : ℚ) =
        if ij.1 = 0 then ((Qwords ij.2).card : ℚ)
        else -((qn ij.1 : ℚ) * ((Qwords ij.2).card : ℚ)) := by
      intro ij _; split_ifs <;> ring
    rw [Finset.sum_congr rfl hcoeff,
        ← Finset.sum_filter_add_sum_filter_not (Finset.antidiagonal m) (fun x => x.1 = 0)]
    have hfilt : (Finset.antidiagonal m).filter (fun x => x.1 = 0) = {(0, m)} := by
      ext ⟨a, b⟩; simp [Finset.mem_antidiagonal]; omega
    rw [hfilt, Finset.sum_singleton]
    simp only [↓reduceIte]
    have hfilt2 : ∀ x ∈ (Finset.antidiagonal m).filter (fun x => ¬x.1 = 0),
        (if x.1 = 0 then ((Qwords x.2).card : ℚ)
         else -((qn x.1 : ℚ) * ((Qwords x.2).card : ℚ))) =
        -((qn x.1 : ℚ) * ((Qwords x.2).card : ℚ)) := by
      intro x hx; simp [(Finset.mem_filter.mp hx).2]
    rw [Finset.sum_congr rfl hfilt2]
    by_cases hm : m = 0
    · subst hm
      have hempty : (Finset.antidiagonal 0).filter (fun x => ¬x.1 = 0) = ∅ := by
        ext ⟨a, b⟩; simp [Finset.mem_antidiagonal]; omega
      rw [hempty, Finset.sum_empty]; simp [Qwords]
    · simp only [hm, ↓reduceIte]
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hfilt3 : (Finset.antidiagonal (m' + 1)).filter (fun x => ¬x.1 = 0) =
          (Finset.range (m' + 1)).image (fun k => (k + 1, m' - k)) := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_image,
                    Finset.mem_range, Prod.mk.injEq]
        constructor
        · intro ⟨hab, ha⟩; exact ⟨a - 1, by omega, by omega, by omega⟩
        · intro ⟨k, hk, hak, hbk⟩; exact ⟨by omega, by omega⟩
      rw [hfilt3, Finset.sum_image (by intro k1 _ k2 _ h; have := Prod.mk.inj h; omega)]
      simp only [Prod.fst, Prod.snd]
      rw [Finset.sum_neg_distrib]
      linarith [Qwords_card_succ_cast' m']
  -- Step 2: QGF = (1-Qps)⁻¹
  have hQGF_inv : QGF = (1 - Qps)⁻¹ := by
    have hconst : PowerSeries.constantCoeff (1 - Qps) ≠ 0 := by simp [Qps]
    rw [PowerSeries.eq_inv_iff_mul_eq_one (φ := QGF) hconst, mul_comm]
    exact h_inv
  -- Step 3: mk Wassembly_card = Pps * QGF
  have hGF : PowerSeries.mk (fun m => ((Wassembly m).card : ℚ)) = Pps * QGF := by
    ext m
    rw [PowerSeries.coeff_mul]
    simp only [hQGF_def, Pps, PowerSeries.coeff_mk]
    -- RHS is ∑ x ∈ antidiag m, (if x.1=0 then 1 else 2) * |Qwords x.2|
    -- Convert to range sum
    have hrhs : ∑ x ∈ Finset.antidiagonal m,
        (if x.1 = 0 then (1 : ℚ) else 2) * ((Qwords x.2).card : ℚ) =
        ∑ r ∈ Finset.range (m + 1),
        (if r = 0 then (1 : ℚ) else 2) * ((Qwords (m - r)).card : ℚ) :=
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => (if i = 0 then (1 : ℚ) else 2) * ((Qwords j).card : ℚ)) (n := m)
    rw [hrhs, Wassembly_card_eq']
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    simp [Passembly, Finset.card_range]
  rw [hGF, hQGF_inv]

/-- From PS_plus_Q_eq_one we get 1 - Q = P·S, so (1-Q)⁻¹ = (P·S)⁻¹.
    Then P · (1-Q)⁻¹ = P · (P·S)⁻¹ = P · S⁻¹ · P⁻¹ = S⁻¹
    (provided P is invertible, which it is since P(0) = 1).

    Proof strategy: From PS_plus_Q_eq_one, derive 1 - Qps = Pps * Sps.
    Then Pps * (1 - Qps)⁻¹ = Pps * (Pps * Sps)⁻¹ = Pps * Sps⁻¹ * Pps⁻¹ = Sps⁻¹.
    Use PowerSeries.mul_inv_cancel for Pps (since Pps constant term = 1). -/
theorem P_div_one_minus_Q_eq_Sps_inv :
    Pps * (1 - Qps)⁻¹ = Sps⁻¹ := by
  have hSps : PowerSeries.constantCoeff Sps ≠ 0 := by
    simp [Sps, sigmaSum]
  have hPS : PowerSeries.constantCoeff (Pps * Sps) ≠ 0 := by
    simp [Pps, Sps, sigmaSum]
  rw [PowerSeries.eq_inv_iff_mul_eq_one hSps]
  have h1 : Pps * Sps = 1 - Qps := by linear_combination PS_plus_Q_eq_one
  rw [← h1]
  have h2 : Pps * Sps * (Pps * Sps)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ hPS
  ring_nf
  exact h2

/-- The generating function of |W_m| (as a power series over ℚ) equals Sps⁻¹.
    Proof: combine Wassembly_gf_eq_P_div_one_minus_Q and P_div_one_minus_Q_eq_Sps_inv. -/
theorem Wassembly_gf_eq_Sps_inv :
    PowerSeries.mk (fun m => ((Wassembly m).card : ℚ)) = Sps⁻¹ := by
  rw [Wassembly_gf_eq_P_div_one_minus_Q, P_div_one_minus_Q_eq_Sps_inv]

/-- **Proposition 2 (`prop:main`).** For every integer $m \geq 0$, the $m$-th coefficient
$c_m$ of $1/S(t)$ equals the number of assemblies $|W_m|$. -/
theorem prop_main (m : ℕ) : cQ m = ((Wassembly m).card : ℚ) := by
  -- Once Wassembly_gf_eq_Sps_inv is proven, this is just reading off coefficients:
  -- cQ m = coeff m (Sps⁻¹) = coeff m (mk (fun m => |W_m|)) = |W_m|
  unfold cQ
  have h := Wassembly_gf_eq_Sps_inv
  rw [← h, PowerSeries.coeff_mk]

/-! ### Helper lemma for positivity -/

/-- W_m is nonempty for all m: take r = m, any U ∈ P_m (which is nonempty since
    |P_m| ≥ 1), and the empty Q-word of weight 0. This gives ((m, U), []) ∈ W_m. -/
theorem Wassembly_nonempty (m : ℕ) : (Wassembly m).Nonempty := by
  refine ⟨((m, 0), []), ?_⟩
  simp only [Wassembly, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  refine ⟨m, Nat.lt_succ_iff.mpr (le_refl m), ?_⟩
  refine ⟨0, ?_, ?_⟩
  · simp only [Passembly, Finset.mem_range]
    split_ifs <;> omega
  · refine ⟨[], ?_, ?_⟩
    · simp [Qwords]
    · simp

/-- Positivity consequence of Proposition 2: $c_m > 0$ for every $m \geq 0$ (since $W_m$ is
nonempty). -/
theorem cQ_pos (m : ℕ) : 0 < cQ m := by
  rw [prop_main]
  have h := Wassembly_nonempty m
  exact_mod_cast Finset.Nonempty.card_pos h

end ColoredRectangles

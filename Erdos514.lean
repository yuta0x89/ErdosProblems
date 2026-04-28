import Mathlib

/-!
# Lean formalization of `erdos_514_comparison_note.tex`

This file formalizes the construction and comparison estimates from
`https://github.com/yuta0x89/ErdosProblems/blob/main/notes/514/erdos_514_third_question_forum_note.tex`.

The main design choices are:

* `Φ : ℝ → ℝ` is a total function.  Its monotonicity and positivity are only
  assumed on `Set.Ici T₀`.
* The radii are fixed once and for all by `r n = n + 2`.  This avoids a second
  inductive choice of radii.
* The path statement is written in a practical epsilon/frequently-small form,
  using paths `γ : ℝ → ℂ` with `‖γ t‖ → ∞` along `atTop`.
* The analytic estimates and the inductive parameter choice are formalized as
  named lemmas, avoiding any additional primitive assumptions.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Erdos514

/-- Lean index `n : ℕ` corresponds to the TeX paper's 1-based index `n + 1`. -/
def N (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ)

/-- Fixed radii.  These satisfy `r n = N n + 1`, hence `r n > N n`. -/
def r (n : ℕ) : ℝ := ((n + 2 : ℕ) : ℝ)

/-- Alternating signs.  This is shifted from the TeX convention but has the same effect. -/
def eps (n : ℕ) : ℝ := (-1 : ℝ) ^ n

lemma N_pos (n : ℕ) : 0 < N n := by
  unfold N
  exact_mod_cast Nat.succ_pos n

lemma r_pos (n : ℕ) : 0 < r n := by
  unfold r
  exact_mod_cast (show (0 : ℕ) < n + 2 by omega)

lemma r_eq_N_add_one (n : ℕ) : r n = N n + 1 := by
  unfold r N
  have h : (n + 2 : ℕ) = (n + 1) + 1 := by omega
  rw [h]
  simp

lemma r_gt_N (n : ℕ) : N n < r n := by
  rw [r_eq_N_add_one n]
  linarith

lemma r_strictMono : StrictMono r := by
  intro m n hmn
  unfold r
  exact_mod_cast Nat.add_lt_add_right hmn 2

lemma r_sub_pos {k n : ℕ} (hkn : k < n) : 0 < r n - r k := by
  exact sub_pos.mpr (r_strictMono hkn)

lemma eps_sq (n : ℕ) : eps n * eps n = 1 := by
  unfold eps
  rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] <;> norm_num

lemma eps_succ (n : ℕ) : eps (n + 1) = - eps n := by
  unfold eps
  rw [pow_succ]
  ring

lemma eps_ne_zero (n : ℕ) : eps n ≠ 0 := by
  intro h
  have hs := eps_sq n
  rw [h] at hs
  norm_num at hs

/-- Auxiliary comparison function.

In the paper this is only used for large `x`; making it total avoids subtype
bookkeeping. -/
def A (Φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  min (Φ (Real.exp x / 2)) (Real.exp x / 4)

lemma A_le_phi (Φ : ℝ → ℝ) (x : ℝ) : A Φ x ≤ Φ (Real.exp x / 2) := by
  -- `A` is a minimum.
  unfold A
  exact min_le_left _ _

lemma A_le_exp_quarter (Φ : ℝ → ℝ) (x : ℝ) : A Φ x ≤ Real.exp x / 4 := by
  -- `A` is a minimum.
  unfold A
  exact min_le_right _ _

lemma exists_x0 (T₀ : ℝ) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x → T₀ ≤ Real.exp x / 2 := by
  let B : ℝ := 2 * max T₀ 1
  refine ⟨max 1 (Real.log B), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro x hx
    have hlog : Real.log B ≤ x := le_trans (le_max_right _ _) hx
    have hBpos : 0 < B := by
      have hmax : 0 < max T₀ 1 := lt_of_lt_of_le zero_lt_one (le_max_right T₀ 1)
      dsimp [B]
      nlinarith
    have hB : B ≤ Real.exp x :=
      (Real.log_le_iff_le_exp hBpos).mp hlog
    have hT : 2 * T₀ ≤ B := by
      dsimp [B]
      nlinarith [le_max_left T₀ 1]
    nlinarith [hB, hT]

lemma tendsto_A_atTop
    (Φ : ℝ → ℝ) (T₀ x₀ : ℝ)
    (hx₀ : ∀ x : ℝ, x₀ ≤ x → T₀ ≤ Real.exp x / 2)
    (hΦ_top : Tendsto Φ atTop atTop) :
    Tendsto (A Φ) atTop atTop := by
  have hexp_half : Tendsto (fun x : ℝ => Real.exp x / 2) atTop atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      Real.tendsto_exp_atTop.const_mul_atTop (show 0 < (1 / 2 : ℝ) by norm_num)
  have hΦ_half : Tendsto (fun x : ℝ => Φ (Real.exp x / 2)) atTop atTop :=
    hΦ_top.comp hexp_half
  have hexp_quarter : Tendsto (fun x : ℝ => Real.exp x / 4) atTop atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      Real.tendsto_exp_atTop.const_mul_atTop (show 0 < (1 / 4 : ℝ) by norm_num)
  rw [Filter.tendsto_atTop_atTop]
  intro C
  rw [Filter.tendsto_atTop_atTop] at hΦ_half hexp_quarter
  obtain ⟨u, hu⟩ := hΦ_half C
  obtain ⟨v, hv⟩ := hexp_quarter C
  refine ⟨max u v, ?_⟩
  intro x hx
  unfold A
  exact le_min
    (hu x (le_trans (le_max_left u v) hx))
    (hv x (le_trans (le_max_right u v) hx))

/-- Parameters of the series.

The fields are exactly the inequalities needed later.  The proof of existence
is by finite induction over the fixed radii `r n = n + 2`.
-/
structure Params (Φ : ℝ → ℝ) (x₀ : ℝ) where
  X : ℕ → ℝ
  lam : ℕ → ℝ
  a : ℕ → ℝ

  lam_pos : ∀ n : ℕ, 0 < lam n
  a_def : ∀ n : ℕ, a n = lam n * r n - X n

  /-- `A(X_n)` is large enough to absorb dyadic constants in later estimates. -/
  A_large : ∀ n : ℕ, (2 : ℝ) ^ (n + 8) ≤ A Φ (X n)

  /-- Growth making the peak values faster than every polynomial. -/
  X_large : ∀ n : ℕ, N n * Real.log (r n) + N n ≤ X n

  /-- Ensures `Real.exp (X n) / 2 ≥ T₀` once `x₀` was chosen. -/
  X_ge_x0 : ∀ n : ℕ, x₀ ≤ X n

  /-- Gives convergence of the series and the needed smallness estimates. -/
  a_large : ∀ n : ℕ, (N n) ^ 2 + lam n * N n ≤ a n

  /-- Off-diagonal estimate at the selected radii. -/
  offdiag : ∀ m n : ℕ, m ≠ n →
    Real.exp (-(a m) + lam m * r n)
      ≤ (1 / 2 : ℝ) ^ (m + n + 10) * A Φ (X n)

/-- A finite initial segment of the parameter construction. -/
structure PartialParams (Φ : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) where
  X : Fin n → ℝ
  lam : Fin n → ℝ
  a : Fin n → ℝ

  lam_pos : ∀ i : Fin n, 0 < lam i
  a_def : ∀ i : Fin n, a i = lam i * r (i : ℕ) - X i
  A_large : ∀ i : Fin n, (2 : ℝ) ^ ((i : ℕ) + 8) ≤ A Φ (X i)
  X_large : ∀ i : Fin n, N (i : ℕ) * Real.log (r (i : ℕ)) + N (i : ℕ) ≤ X i
  X_ge_x0 : ∀ i : Fin n, x₀ ≤ X i
  a_large : ∀ i : Fin n, (N (i : ℕ)) ^ 2 + lam i * N (i : ℕ) ≤ a i
  offdiag : ∀ i j : Fin n, (i : ℕ) ≠ (j : ℕ) →
    Real.exp (-(a i) + lam i * r (j : ℕ))
      ≤ (1 / 2 : ℝ) ^ ((i : ℕ) + (j : ℕ) + 10) * A Φ (X j)

namespace PartialParams

def nil (Φ : ℝ → ℝ) (x₀ : ℝ) : PartialParams Φ x₀ 0 where
  X := Fin.elim0
  lam := Fin.elim0
  a := Fin.elim0
  lam_pos := by intro i; exact Fin.elim0 i
  a_def := by intro i; exact Fin.elim0 i
  A_large := by intro i; exact Fin.elim0 i
  X_large := by intro i; exact Fin.elim0 i
  X_ge_x0 := by intro i; exact Fin.elim0 i
  a_large := by intro i; exact Fin.elim0 i
  offdiag := by intro i; exact Fin.elim0 i

structure Extends {Φ : ℝ → ℝ} {x₀ : ℝ} {n : ℕ}
    (P : PartialParams Φ x₀ n) (Q : PartialParams Φ x₀ (n + 1)) : Prop where
  X_eq : ∀ i : Fin n, Q.X (Fin.castSucc i) = P.X i
  lam_eq : ∀ i : Fin n, Q.lam (Fin.castSucc i) = P.lam i
  a_eq : ∀ i : Fin n, Q.a (Fin.castSucc i) = P.a i

lemma extend
    {Φ : ℝ → ℝ} {x₀ : ℝ} {n : ℕ}
    (hA_top : Tendsto (A Φ) atTop atTop)
    (P : PartialParams Φ x₀ n) :
    ∃ Q : PartialParams Φ x₀ (n + 1), Extends P Q := by
  classical

  have hXlarge_ev : ∀ᶠ x in atTop,
      N n * Real.log (r n) + N n ≤ x :=
    eventually_ge_atTop _
  have hx0_ev : ∀ᶠ x in atTop, x₀ ≤ x :=
    eventually_ge_atTop _
  have hAX_ev : ∀ᶠ x in atTop, (2 : ℝ) ^ (n + 8) ≤ A Φ x :=
    hA_top.eventually_ge_atTop _
  have hOld_ev : ∀ᶠ x in atTop, ∀ i : Fin n,
      Real.exp (-(P.a i) + P.lam i * r n) /
          ((1 / 2 : ℝ) ^ ((i : ℕ) + n + 10)) ≤ A Φ x := by
    exact eventually_all.mpr fun i => hA_top.eventually_ge_atTop _

  obtain ⟨Xn, hXlarge_n, hx0_n, hAX_n, hOld_n⟩ :=
    (hXlarge_ev.and (hx0_ev.and (hAX_ev.and hOld_ev))).exists

  have hOldToNew : ∀ i : Fin n,
      Real.exp (-(P.a i) + P.lam i * r n)
        ≤ (1 / 2 : ℝ) ^ ((i : ℕ) + n + 10) * A Φ Xn := by
    intro i
    have hq : 0 < (1 / 2 : ℝ) ^ ((i : ℕ) + n + 10) := by
      positivity
    have h := (div_le_iff₀ hq).mp (hOld_n i)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h

  have hCpos : ∀ i : Fin n,
      0 < (1 / 2 : ℝ) ^ (n + (i : ℕ) + 10) * A Φ (P.X i) := by
    intro i
    have hq : 0 < (1 / 2 : ℝ) ^ (n + (i : ℕ) + 10) := by
      positivity
    have hpow : 0 < (2 : ℝ) ^ ((i : ℕ) + 8) := by
      positivity
    have hApos : 0 < A Φ (P.X i) := lt_of_lt_of_le hpow (P.A_large i)
    exact mul_pos hq hApos

  have hLamPos_ev : ∀ᶠ L in atTop, (0 : ℝ) < L :=
    eventually_gt_atTop _
  have hLamLarge_ev : ∀ᶠ L in atTop, Xn + (N n) ^ 2 ≤ L :=
    eventually_ge_atTop _
  have hLamOld_ev : ∀ᶠ L in atTop, ∀ i : Fin n,
      (Xn - Real.log ((1 / 2 : ℝ) ^ (n + (i : ℕ) + 10) * A Φ (P.X i))) /
          (r n - r (i : ℕ)) ≤ L := by
    exact eventually_all.mpr fun i => eventually_ge_atTop _

  obtain ⟨lamn, hlam_pos, hlam_large, hlam_old⟩ :=
    (hLamPos_ev.and (hLamLarge_ev.and hLamOld_ev)).exists

  let an : ℝ := lamn * r n - Xn

  have hNewToOld : ∀ i : Fin n,
      Real.exp (-an + lamn * r (i : ℕ))
        ≤ (1 / 2 : ℝ) ^ (n + (i : ℕ) + 10) * A Φ (P.X i) := by
    intro i
    let c : ℝ := (1 / 2 : ℝ) ^ (n + (i : ℕ) + 10) * A Φ (P.X i)
    have hcpos : 0 < c := by
      simpa [c] using hCpos i
    have hd : 0 < r n - r (i : ℕ) := r_sub_pos i.2
    have hdiv : (Xn - Real.log c) / (r n - r (i : ℕ)) ≤ lamn := by
      simpa [c] using hlam_old i
    have hmul : Xn - Real.log c ≤ lamn * (r n - r (i : ℕ)) :=
      (div_le_iff₀ hd).mp hdiv
    have harg : -an + lamn * r (i : ℕ) ≤ Real.log c := by
      dsimp [an]
      nlinarith
    have hexp : Real.exp (-an + lamn * r (i : ℕ)) ≤ Real.exp (Real.log c) :=
      Real.exp_le_exp.mpr harg
    calc
      Real.exp (-an + lamn * r (i : ℕ)) ≤ Real.exp (Real.log c) := hexp
      _ = c := Real.exp_log hcpos

  let Q : PartialParams Φ x₀ (n + 1) :=
    { X := Fin.snoc P.X Xn
      lam := Fin.snoc P.lam lamn
      a := Fin.snoc P.a an

      lam_pos := by
        intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa using hlam_pos
        · simpa using P.lam_pos i

      a_def := by
        intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa [an]
        · simpa using P.a_def i

      A_large := by
        intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa using hAX_n
        · simpa using P.A_large i

      X_large := by
        intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa using hXlarge_n
        · simpa using P.X_large i

      X_ge_x0 := by
        intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa using hx0_n
        · simpa using P.X_ge_x0 i

      a_large := by
        intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simp [an, r_eq_N_add_one]
          nlinarith
        · simpa using P.a_large i

      offdiag := by
        intro i
        refine Fin.lastCases ?_ (fun i0 => ?_) i
        · intro j
          refine Fin.lastCases ?_ (fun j0 => ?_) j
          · intro hij
            exfalso
            exact hij rfl
          · intro hij
            simpa using hNewToOld j0
        · intro j
          refine Fin.lastCases ?_ (fun j0 => ?_) j
          · intro hij
            simpa using hOldToNew i0
          · intro hij
            have hij0 : (i0 : ℕ) ≠ (j0 : ℕ) := by
              intro h
              exact hij h
            simpa using P.offdiag i0 j0 hij0 }

  refine ⟨Q, ?_⟩
  exact
    { X_eq := by intro i; simp [Q]
      lam_eq := by intro i; simp [Q]
      a_eq := by intro i; simp [Q] }

lemma stable
    {Φ : ℝ → ℝ} {x₀ : ℝ}
    (S : ∀ n : ℕ, PartialParams Φ x₀ n)
    (hS : ∀ n : ℕ, Extends (S n) (S (n + 1))) :
    ∀ n k : ℕ, ∀ hk : k < n,
      (S n).X ⟨k, hk⟩ = (S (k + 1)).X (Fin.last k) ∧
      (S n).lam ⟨k, hk⟩ = (S (k + 1)).lam (Fin.last k) ∧
      (S n).a ⟨k, hk⟩ = (S (k + 1)).a (Fin.last k) := by
  intro n
  induction n with
  | zero =>
      intro k hk
      exact False.elim (Nat.not_lt_zero k hk)
  | succ n ih =>
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk_eq
      · have hfin : (⟨k, hk⟩ : Fin (n + 1)) = Fin.castSucc (⟨k, hk'⟩ : Fin n) := by
          apply Fin.ext
          simp
        have hrec := ih k hk'
        constructor
        · rw [hfin, (hS n).X_eq ⟨k, hk'⟩, hrec.1]
        · constructor
          · rw [hfin, (hS n).lam_eq ⟨k, hk'⟩, hrec.2.1]
          · rw [hfin, (hS n).a_eq ⟨k, hk'⟩, hrec.2.2]
      · have hfin : (⟨k, hk⟩ : Fin (n + 1)) = Fin.last n := by
          apply Fin.ext
          exact hk_eq
        constructor
        · rw [hfin, hk_eq]
        · constructor <;> rw [hfin, hk_eq]

end PartialParams

lemma exists_params
    (Φ : ℝ → ℝ) (x₀ : ℝ)
    (hA_top : Tendsto (A Φ) atTop atTop) :
    ∃ P : Params Φ x₀, True := by
  classical

  let step : ∀ n : ℕ, PartialParams Φ x₀ n → PartialParams Φ x₀ (n + 1) :=
    fun n P => Classical.choose (PartialParams.extend hA_top P)

  let S : ∀ n : ℕ, PartialParams Φ x₀ n :=
    Nat.rec (PartialParams.nil Φ x₀) step

  have hS : ∀ n : ℕ, PartialParams.Extends (S n) (S (n + 1)) := by
    intro n
    change PartialParams.Extends (S n) (step n (S n))
    exact Classical.choose_spec (PartialParams.extend hA_top (S n))

  let X : ℕ → ℝ := fun n => (S (n + 1)).X (Fin.last n)
  let lam : ℕ → ℝ := fun n => (S (n + 1)).lam (Fin.last n)
  let a : ℕ → ℝ := fun n => (S (n + 1)).a (Fin.last n)

  have hstable := PartialParams.stable S hS

  refine ⟨?P, trivial⟩
  exact
    { X := X
      lam := lam
      a := a

      lam_pos := by
        intro n
        dsimp [lam]
        exact (S (n + 1)).lam_pos (Fin.last n)

      a_def := by
        intro n
        dsimp [X, lam, a]
        simpa using (S (n + 1)).a_def (Fin.last n)

      A_large := by
        intro n
        dsimp [X]
        simpa using (S (n + 1)).A_large (Fin.last n)

      X_large := by
        intro n
        dsimp [X]
        simpa using (S (n + 1)).X_large (Fin.last n)

      X_ge_x0 := by
        intro n
        dsimp [X]
        simpa using (S (n + 1)).X_ge_x0 (Fin.last n)

      a_large := by
        intro n
        dsimp [lam, a]
        simpa using (S (n + 1)).a_large (Fin.last n)

      offdiag := by
        intro m n hmn
        let K : ℕ := Nat.max m n + 1
        have hmK : m < K := by
          dsimp [K]
          exact Nat.lt_succ_of_le (Nat.le_max_left m n)
        have hnK : n < K := by
          dsimp [K]
          exact Nat.lt_succ_of_le (Nat.le_max_right m n)
        have hm_stable := hstable K m hmK
        have hn_stable := hstable K n hnK
        have hmn_fin : ((⟨m, hmK⟩ : Fin K) : ℕ) ≠ ((⟨n, hnK⟩ : Fin K) : ℕ) := by
          simpa using hmn
        have h := (S K).offdiag ⟨m, hmK⟩ ⟨n, hnK⟩ hmn_fin
        rw [hm_stable.2.2, hm_stable.2.1, hn_stable.1] at h
        simpa [X, lam, a, K] using h }

/-- The `n`-th exponential term. -/
def term {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀) (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (((-(P.a n) : ℝ) : ℂ) + (((eps n * P.lam n) : ℝ) : ℂ) * z)

/-- The constructed entire function. -/
def f {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀) : ℂ → ℂ :=
  fun z => ∑' n : ℕ, term P n z

/-- Peak point on the `n`-th circle. -/
def zPeak (n : ℕ) : ℂ := ((eps n * r n : ℝ) : ℂ)

lemma abs_eps (n : ℕ) : |eps n| = 1 := by
  unfold eps
  exact abs_neg_one_pow n

lemma norm_zPeak (n : ℕ) : ‖zPeak n‖ = r n := by
  unfold zPeak
  rw [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_mul, abs_eps n, abs_of_pos (r_pos n)]
  norm_num

lemma term_norm_le_exp_norm
    {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀) (n : ℕ) (z : ℂ) :
    ‖term P n z‖ ≤ Real.exp (-(P.a n) + P.lam n * ‖z‖) := by
  unfold term
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_mul, add_zero]
  have hzre : eps n * z.re ≤ ‖z‖ := by
    calc
      eps n * z.re ≤ |eps n * z.re| := le_abs_self _
      _ = |eps n| * |z.re| := abs_mul _ _
      _ = 1 * |z.re| := by rw [abs_eps n]
      _ = |z.re| := by ring
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hmul := mul_le_mul_of_nonneg_left hzre (le_of_lt (P.lam_pos n))
  nlinarith [hmul]

lemma term_at_peak
    {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀) (n : ℕ) :
    term P n (zPeak n) = Complex.exp ((P.X n : ℝ) : ℂ) := by
  unfold term zPeak
  apply congrArg Complex.exp
  rw [P.a_def n]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_add]
  congr 1
  have hsq : eps n ^ 2 = 1 := by
    simpa [pow_two] using eps_sq n
  ring_nf
  rw [hsq]
  ring

lemma norm_term_at_peak
    {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀) (n : ℕ) :
    ‖term P n (zPeak n)‖ = Real.exp (P.X n) := by
  rw [term_at_peak P n]
  exact Complex.norm_exp_ofReal (P.X n)

/-- Closed-disk maximum.  This is more convenient than the circle maximum in the main proof. -/
def Mc (g : ℂ → ℂ) (R : ℝ) : ℝ :=
  sSup { y : ℝ | ∃ z : ℂ, ‖z‖ ≤ R ∧ y = ‖g z‖ }

/-- Circle maximum, matching the TeX definition. -/
def Ms (g : ℂ → ℂ) (R : ℝ) : ℝ :=
  sSup { y : ℝ | ∃ z : ℂ, ‖z‖ = R ∧ y = ‖g z‖ }

/-- Pure order-theoretic monotonicity of `Mc`, with the hypotheses needed by
`csSup_le_csSup` on a conditionally complete lattice. -/
lemma Mc_mono_of_nonempty_bddAbove
    (g : ℂ → ℂ) {R S : ℝ} (hRS : R ≤ S)
    (hR_nonempty :
      { y : ℝ | ∃ z : ℂ, ‖z‖ ≤ R ∧ y = ‖g z‖ }.Nonempty)
    (hS_bdd :
      BddAbove { y : ℝ | ∃ z : ℂ, ‖z‖ ≤ S ∧ y = ‖g z‖ }) :
    Mc g R ≤ Mc g S := by
  unfold Mc
  exact csSup_le_csSup hS_bdd hR_nonempty (by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z, hz.trans hRS, rfl⟩)

/-- The set of values defining `Mc g R` is bounded above when `g` is continuous. -/
lemma Mc_bddAbove_of_continuous
    (g : ℂ → ℂ) (hg : Continuous g) (R : ℝ) :
    BddAbove { y : ℝ | ∃ z : ℂ, ‖z‖ ≤ R ∧ y = ‖g z‖ } := by
  let h : ℂ → ℝ := fun z => ‖g z‖
  have hcont : Continuous h := continuous_norm.comp hg
  have hcompact : IsCompact (h '' Metric.closedBall (0 : ℂ) R) :=
    (isCompact_closedBall (0 : ℂ) R).image hcont
  have hbounded : Bornology.IsBounded (h '' Metric.closedBall (0 : ℂ) R) :=
    hcompact.isBounded
  refine hbounded.bddAbove.mono ?_
  rintro y ⟨z, hz, rfl⟩
  refine ⟨z, ?_, rfl⟩
  simpa [h, Metric.mem_closedBall, dist_eq_norm] using hz

/-- Monotonicity of the closed-disk maximum for continuous functions.

The continuity and nonnegative-radius assumptions are needed because `sSup` on
`ℝ` is totalized in Lean: for an unbounded set it is definitionally the same as
`sSup ∅` rather than `+∞`.  Thus the statement without boundedness hypotheses is
false for arbitrary discontinuous `g`. -/
lemma Mc_mono (g : ℂ → ℂ) (hg : Continuous g) {R S : ℝ}
    (hR : 0 ≤ R) (hRS : R ≤ S) :
    Mc g R ≤ Mc g S := by
  refine Mc_mono_of_nonempty_bddAbove g hRS ?_ (Mc_bddAbove_of_continuous g hg S)
  refine ⟨‖g 0‖, ?_⟩
  refine ⟨0, ?_, rfl⟩
  simpa using hR

lemma norm_le_Mc
    (g : ℂ → ℂ) (hg : Continuous g) {z : ℂ} {R : ℝ}
    (hz : ‖z‖ ≤ R) :
    ‖g z‖ ≤ Mc g R := by
  unfold Mc
  exact le_csSup (Mc_bddAbove_of_continuous g hg R) ⟨z, hz, rfl⟩

/-- A locally uniform summability lemma for the constructed exponential series. -/
lemma term_summableLocallyUniformlyOn
    {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀) :
    SummableLocallyUniformlyOn (fun n z => term P n z) Set.univ := by
  refine SummableLocallyUniformlyOn.of_locally_bounded_eventually
    (f := fun n z => term P n z) isOpen_univ ?_
  intro K _hK hKc
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  refine ⟨fun n : ℕ => Real.exp (-(n : ℝ)), Real.summable_exp_neg_nat, ?_⟩
  have hRN_atTop : ∀ᶠ n : ℕ in atTop, R ≤ N n := by
    obtain ⟨m, hm⟩ := exists_nat_gt R
    refine eventually_atTop.2 ⟨m, ?_⟩
    intro n hmn
    have hm_le_n : (m : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hmn
    have hn_le_N : (n : ℝ) ≤ N n := by
      unfold N
      exact_mod_cast (show n ≤ n + 1 by omega)
    exact (le_of_lt hm).trans (hm_le_n.trans hn_le_N)
  have hRN : ∀ᶠ n : ℕ in cofinite, R ≤ N n := by
    rw [Nat.cofinite_eq_atTop]
    exact hRN_atTop
  filter_upwards [hRN] with n hn z hz
  have hzN : ‖z‖ ≤ N n := (hR z hz).trans hn
  have hmulnorm : P.lam n * ‖z‖ ≤ P.lam n * N n :=
    mul_le_mul_of_nonneg_left hzN (le_of_lt (P.lam_pos n))
  have hexponent : -(P.a n) + P.lam n * ‖z‖ ≤ -((N n) ^ 2) := by
    calc
      -(P.a n) + P.lam n * ‖z‖
          ≤ -((N n) ^ 2 + P.lam n * N n) + P.lam n * N n := by
            exact add_le_add (neg_le_neg (P.a_large n)) hmulnorm
      _ = -((N n) ^ 2) := by
            ring
  have hN_ge_one : (1 : ℝ) ≤ N n := by
    unfold N
    exact_mod_cast (show (1 : ℕ) ≤ n + 1 by omega)
  have hN_nonneg : 0 ≤ N n := (zero_le_one.trans hN_ge_one)
  have hN_sq_ge : N n ≤ (N n) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hN_ge_one hN_nonneg
    simpa [pow_two] using hmul
  have hN_ge_nat : (n : ℝ) ≤ N n := by
    unfold N
    exact_mod_cast (show n ≤ n + 1 by omega)
  calc
    ‖term P n z‖
        ≤ Real.exp (-(P.a n) + P.lam n * ‖z‖) :=
          term_norm_le_exp_norm P n z
    _ ≤ Real.exp (-((N n) ^ 2)) :=
          Real.exp_le_exp.mpr hexponent
    _ ≤ Real.exp (-(N n)) :=
          Real.exp_le_exp.mpr (neg_le_neg hN_sq_ge)
    _ ≤ Real.exp (-(n : ℝ)) :=
          Real.exp_le_exp.mpr (neg_le_neg hN_ge_nat)

lemma f_differentiable
    {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀) :
    Differentiable ℂ (f P) := by
  apply differentiableOn_univ.mp
  change DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℕ, term P n z) Set.univ
  refine SummableLocallyUniformlyOn.differentiableOn isOpen_univ
    (term_summableLocallyUniformlyOn P) ?_
  intro n z _hz
  change DifferentiableAt ℂ
    (fun w : ℂ =>
      Complex.exp (((-(P.a n) : ℝ) : ℂ) + (((eps n * P.lam n) : ℝ) : ℂ) * w)) z
  simpa [Complex.ofReal_mul] using
    ((differentiableAt_const (((-(P.a n) : ℝ) : ℂ)) :
          DifferentiableAt ℂ (fun _ : ℂ => (((-(P.a n) : ℝ) : ℂ))) z).add
      ((differentiableAt_const ((((eps n * P.lam n) : ℝ) : ℂ)) :
          DifferentiableAt ℂ
            (fun _ : ℂ => ((((eps n * P.lam n) : ℝ) : ℂ))) z).mul
        (differentiableAt_id : DifferentiableAt ℂ (fun w : ℂ => w) z))).cexp

/-- Entire and not a polynomial.  This is the working definition used here. -/
def TranscendentalEntire (g : ℂ → ℂ) : Prop :=
  Differentiable ℂ g ∧ ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, p.eval z = g z

lemma polynomial_point_bound (p : Polynomial ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ →
      ‖p.eval z‖ ≤ C * ‖z‖ ^ p.natDegree := by
  classical
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _hi => norm_nonneg (p.coeff i))
  · intro z hz
    calc
      ‖p.eval z‖
          = ‖∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * z ^ i‖ := by
            rw [Polynomial.eval_eq_sum_range (p := p) z]
      _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i * z ^ i‖ :=
            norm_sum_le (Finset.range (p.natDegree + 1))
              (fun i : ℕ => p.coeff i * z ^ i)
      _ = ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ * ‖z‖ ^ i := by
            simp
      _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1),
            ‖p.coeff i‖ * ‖z‖ ^ p.natDegree := by
            apply Finset.sum_le_sum
            intro i hi
            have hi_le : i ≤ p.natDegree := by
              exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have hpow : ‖z‖ ^ i ≤ ‖z‖ ^ p.natDegree := by
              exact pow_le_pow_right₀ hz hi_le
            exact mul_le_mul_of_nonneg_left hpow (norm_nonneg (p.coeff i))
      _ = (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) *
            ‖z‖ ^ p.natDegree := by
            rw [Finset.sum_mul]

lemma offdiag_norm_at_peak
    {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀)
    {m n : ℕ} (hmn : m ≠ n) :
    ‖term P m (zPeak n)‖
      ≤ (1 / 2 : ℝ) ^ (m + n + 10) * A Φ (P.X n) := by
  calc
    ‖term P m (zPeak n)‖
        ≤ Real.exp (-(P.a m) + P.lam m * ‖zPeak n‖) :=
          term_norm_le_exp_norm P m (zPeak n)
    _ = Real.exp (-(P.a m) + P.lam m * r n) := by rw [norm_zPeak n]
    _ ≤ (1 / 2 : ℝ) ^ (m + n + 10) * A Φ (P.X n) := P.offdiag m n hmn

lemma offdiag_sum_at_peak
    {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀) (n : ℕ) :
    (∑' m : ℕ, if m = n then 0 else ‖term P m (zPeak n)‖)
      ≤ (1 / 2 : ℝ) ^ (n + 6) * A Φ (P.X n) := by
  let q : ℝ := (1 / 2 : ℝ)
  let B : ℝ := A Φ (P.X n)
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    norm_num
  have hq_le_one : q ≤ 1 := by
    dsimp [q]
    norm_num
  have hB_nonneg : 0 ≤ B := by
    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (n + 8) :=
      pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n + 8)
    exact hpow_nonneg.trans (by simpa [B] using P.A_large n)

  let c : ℝ := q ^ (n + 10) * B
  have hc_nonneg : 0 ≤ c := by
    exact mul_nonneg (pow_nonneg hq_nonneg (n + 10)) hB_nonneg

  let u : ℕ → ℝ := fun m => if m = n then 0 else ‖term P m (zPeak n)‖
  let v : ℕ → ℝ := fun m => c * q ^ m

  have hv_summable : Summable v := by
    dsimp [v, q]
    exact summable_geometric_two.mul_left c

  have hu_nonneg : ∀ m : ℕ, 0 ≤ u m := by
    intro m
    by_cases hmn : m = n
    · simp [u, hmn]
    · simpa [u, hmn] using (norm_nonneg (term P m (zPeak n)))

  have huv_le : ∀ m : ℕ, u m ≤ v m := by
    intro m
    by_cases hmn : m = n
    · have hv_nonneg : 0 ≤ v m := by
        dsimp [v]
        exact mul_nonneg hc_nonneg (pow_nonneg hq_nonneg m)
      simpa [u, hmn] using hv_nonneg
    · have hm : ‖term P m (zPeak n)‖ ≤ q ^ (m + n + 10) * B := by
        simpa [q, B] using offdiag_norm_at_peak P hmn
      have hpoweq : q ^ (m + n + 10) * B = c * q ^ m := by
        dsimp [c]
        have hnat : m + n + 10 = (n + 10) + m := by omega
        rw [hnat, pow_add]
        ring
      have hm' : ‖term P m (zPeak n)‖ ≤ c * q ^ m := hm.trans_eq hpoweq
      simpa [u, v, hmn] using hm'

  have hu_summable : Summable u :=
    Summable.of_nonneg_of_le hu_nonneg huv_le hv_summable

  have htsum_le : (∑' m : ℕ, u m) ≤ ∑' m : ℕ, v m :=
    Summable.tsum_le_tsum huv_le hu_summable hv_summable

  have hv_tsum : (∑' m : ℕ, v m) = c * 2 := by
    dsimp [v, q]
    rw [_root_.tsum_mul_left, tsum_geometric_two]

  have hmajor_le : c * 2 ≤ q ^ (n + 6) * B := by
    have hpow_le : q ^ (n + 9) ≤ q ^ (n + 6) := by
      exact pow_le_pow_of_le_one hq_nonneg hq_le_one (by omega)
    have hsucc : q ^ (n + 10) = q ^ (n + 9) * q := by
      have hnat : n + 10 = (n + 9) + 1 := by omega
      rw [hnat, pow_succ]
    calc
      c * 2 = (q ^ (n + 10) * B) * 2 := by rfl
      _ = (q ^ (n + 10) * 2) * B := by ring
      _ = q ^ (n + 9) * B := by
        rw [hsucc]
        dsimp [q]
        ring
      _ ≤ q ^ (n + 6) * B :=
        mul_le_mul_of_nonneg_right hpow_le hB_nonneg

  have hfinal : (∑' m : ℕ, u m) ≤ q ^ (n + 6) * B := by
    calc
      (∑' m : ℕ, u m) ≤ ∑' m : ℕ, v m := htsum_le
      _ = c * 2 := hv_tsum
      _ ≤ q ^ (n + 6) * B := hmajor_le
  simpa [u, q, B] using hfinal

lemma f_peak_lower
    {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀) (n : ℕ) :
    Real.exp (P.X n) / 2 ≤ ‖f P (zPeak n)‖ := by
  let z : ℂ := zPeak n
  let q : ℝ := (1 / 2 : ℝ)
  let B : ℝ := A Φ (P.X n)

  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    norm_num
  have hq_le_one : q ≤ 1 := by
    dsimp [q]
    norm_num
  have hB_nonneg : 0 ≤ B := by
    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (n + 8) :=
      pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n + 8)
    exact hpow_nonneg.trans (by simpa [B] using P.A_large n)

  let tail : ℕ → ℂ := fun m => if m = n then 0 else term P m z
  let u : ℕ → ℝ := fun m => if m = n then 0 else ‖term P m z‖
  have hu_nonneg : ∀ m : ℕ, 0 ≤ u m := by
    intro m
    by_cases hmn : m = n
    · simp [u, hmn]
    · simpa [u, hmn] using (norm_nonneg (term P m z))

  let c : ℝ := q ^ (n + 10) * B
  have hc_nonneg : 0 ≤ c := by
    exact mul_nonneg (pow_nonneg hq_nonneg (n + 10)) hB_nonneg
  let v : ℕ → ℝ := fun m => c * q ^ m
  have hv_summable : Summable v := by
    dsimp [v, q]
    exact summable_geometric_two.mul_left c

  have huv_le : ∀ m : ℕ, u m ≤ v m := by
    intro m
    by_cases hmn : m = n
    · have hv_nonneg : 0 ≤ v m := by
        dsimp [v]
        exact mul_nonneg hc_nonneg (pow_nonneg hq_nonneg m)
      simpa [u, hmn] using hv_nonneg
    · have hm : ‖term P m z‖ ≤ q ^ (m + n + 10) * B := by
        simpa [z, q, B] using offdiag_norm_at_peak P hmn
      have hpoweq : q ^ (m + n + 10) * B = c * q ^ m := by
        dsimp [c]
        have hnat : m + n + 10 = (n + 10) + m := by omega
        rw [hnat, pow_add]
        ring
      have hm' : ‖term P m z‖ ≤ c * q ^ m := hm.trans_eq hpoweq
      simpa [u, v, hmn] using hm'

  have hu_summable : Summable u :=
    Summable.of_nonneg_of_le hu_nonneg huv_le hv_summable

  have htail_norm_le : ∀ m : ℕ, ‖tail m‖ ≤ u m := by
    intro m
    by_cases hmn : m = n
    · simp [tail, u, hmn]
    · simp [tail, u, hmn]
  have htail_summable : Summable tail :=
    Summable.of_norm_bounded hu_summable htail_norm_le

  have htail_bound : ‖∑' m : ℕ, tail m‖ ≤ q ^ (n + 6) * B := by
    have htail_norm_bound : ‖∑' m : ℕ, tail m‖ ≤ ∑' m : ℕ, u m :=
      tsum_of_norm_bounded hu_summable.hasSum htail_norm_le
    calc
      ‖∑' m : ℕ, tail m‖ ≤ ∑' m : ℕ, u m := htail_norm_bound
      _ ≤ q ^ (n + 6) * B := by
        simpa [u, q, B, z] using offdiag_sum_at_peak P n

  let single : ℕ → ℂ := fun m => if m = n then term P n z else 0
  have hsingle_hasSum : HasSum single (term P n z) := by
    simpa [single] using (hasSum_ite_eq n (term P n z))
  have hsum_terms : HasSum (fun m : ℕ => term P m z)
      (term P n z + ∑' m : ℕ, tail m) := by
    refine (hsingle_hasSum.add htail_summable.hasSum).congr_fun ?_
    intro m
    by_cases hmn : m = n
    · simp [single, tail, hmn]
    · simp [single, tail, hmn]
  have hdecomp : f P z = term P n z + ∑' m : ℕ, tail m := by
    unfold f
    exact hsum_terms.tsum_eq

  have hmain_norm : ‖term P n z‖ = Real.exp (P.X n) := by
    simpa [z] using norm_term_at_peak P n

  have hpow_le_one : q ^ (n + 6) ≤ 1 := by
    have h := pow_le_pow_of_le_one hq_nonneg hq_le_one (show 0 ≤ n + 6 by omega)
    simpa using h

  have htail_small : ‖∑' m : ℕ, tail m‖ ≤ Real.exp (P.X n) / 2 := by
    have hA_le : B ≤ Real.exp (P.X n) / 4 := by
      simpa [B] using A_le_exp_quarter Φ (P.X n)
    calc
      ‖∑' m : ℕ, tail m‖ ≤ q ^ (n + 6) * B := htail_bound
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right hpow_le_one hB_nonneg
      _ = B := by ring
      _ ≤ Real.exp (P.X n) / 4 := hA_le
      _ ≤ Real.exp (P.X n) / 2 := by
        nlinarith [Real.exp_pos (P.X n)]

  have hmain_eq : term P n z = f P z - ∑' m : ℕ, tail m := by
    rw [hdecomp]
    abel
  have hreverse : ‖term P n z‖ - ‖∑' m : ℕ, tail m‖ ≤ ‖f P z‖ := by
    have hmain_le : ‖term P n z‖ ≤ ‖f P z‖ + ‖∑' m : ℕ, tail m‖ := by
      calc
        ‖term P n z‖ = ‖f P z - ∑' m : ℕ, tail m‖ := by rw [hmain_eq]
        _ ≤ ‖f P z‖ + ‖∑' m : ℕ, tail m‖ := norm_sub_le _ _
    linarith
  have htarget : Real.exp (P.X n) / 2 ≤ ‖term P n z‖ - ‖∑' m : ℕ, tail m‖ := by
    rw [hmain_norm]
    linarith [htail_small]
  exact htarget.trans hreverse

lemma Mc_peak_lower
    {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀) (n : ℕ) :
    Real.exp (P.X n) / 2 ≤ Mc (f P) (r n) := by
  have hz : ‖zPeak n‖ ≤ r n := by
    rw [norm_zPeak n]
  exact (f_peak_lower P n).trans
    (norm_le_Mc (f P) (f_differentiable P).continuous hz)

lemma f_not_polynomial
    {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀) :
    ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, p.eval z = f P z := by
  rintro ⟨p, hp⟩
  obtain ⟨C, hC_nonneg, hbound⟩ := polynomial_point_bound p

  -- Choose an index for which the exponential factor beats the polynomial
  -- constant, and whose construction index dominates the polynomial degree.
  obtain ⟨nC, hnC⟩ := exists_nat_gt (Real.log (2 * C + 1))
  let n : ℕ := max nC p.natDegree

  have hnC_le_n : nC ≤ n := by
    dsimp [n]
    exact Nat.le_max_left _ _
  have hdeg_le_n : p.natDegree ≤ n := by
    dsimp [n]
    exact Nat.le_max_right _ _
  have hdeg_le_succ : p.natDegree ≤ n + 1 :=
    hdeg_le_n.trans (Nat.le_succ n)

  have hlog_lt_N : Real.log (2 * C + 1) < N n := by
    have hnC_le_N : (nC : ℝ) ≤ N n := by
      unfold N
      exact_mod_cast hnC_le_n.trans (Nat.le_succ n)
    exact lt_of_lt_of_le hnC hnC_le_N

  have htwoC_add_one_pos : 0 < 2 * C + 1 := by
    nlinarith [hC_nonneg]
  have htwoC_lt_expN : 2 * C < Real.exp (N n) := by
    have hlt_log : 2 * C < Real.exp (Real.log (2 * C + 1)) := by
      rw [Real.exp_log htwoC_add_one_pos]
      linarith
    have hlt_exp : Real.exp (Real.log (2 * C + 1)) < Real.exp (N n) :=
      Real.exp_lt_exp.mpr hlog_lt_N
    exact hlt_log.trans hlt_exp
  have hC_lt_expN_half : C < Real.exp (N n) / 2 := by
    nlinarith [htwoC_lt_expN]

  have hr_one : 1 ≤ r n := by
    unfold r
    exact_mod_cast (show (1 : ℕ) ≤ n + 2 by omega)
  have hz_one : 1 ≤ ‖zPeak n‖ := by
    rw [norm_zPeak n]
    exact hr_one

  -- The polynomial upper bound at the peak point.
  have hupper : ‖f P (zPeak n)‖ ≤ C * r n ^ p.natDegree := by
    have h := hbound (zPeak n) hz_one
    rw [hp (zPeak n)] at h
    simpa [norm_zPeak n] using h

  -- Turn the built-in logarithmic lower bound on `P.X n` into the explicit
  -- comparison with the polynomial power of `r n`.
  have hbase :
      Real.exp (N n * Real.log (r n) + N n) =
        r n ^ (n + 1) * Real.exp (N n) := by
    unfold N
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (r_pos n)]

  have hmain_le_expX :
      r n ^ (n + 1) * Real.exp (N n) ≤ Real.exp (P.X n) := by
    have h := Real.exp_le_exp.mpr (P.X_large n)
    rwa [hbase] at h

  have hpow_le : r n ^ p.natDegree ≤ r n ^ (n + 1) := by
    exact pow_le_pow_right₀ hr_one hdeg_le_succ

  have hpoly_lt_peak : C * r n ^ p.natDegree < Real.exp (P.X n) / 2 := by
    calc
      C * r n ^ p.natDegree ≤ C * r n ^ (n + 1) := by
        exact mul_le_mul_of_nonneg_left hpow_le hC_nonneg
      _ < (Real.exp (N n) / 2) * r n ^ (n + 1) := by
        exact mul_lt_mul_of_pos_right hC_lt_expN_half (pow_pos (r_pos n) (n + 1))
      _ = (r n ^ (n + 1) * Real.exp (N n)) / 2 := by
        ring
      _ ≤ Real.exp (P.X n) / 2 := by
        nlinarith [hmain_le_expX]

  -- But the peak lower bound gives the opposite inequality.
  have hpeak_le_poly : Real.exp (P.X n) / 2 ≤ C * r n ^ p.natDegree :=
    (f_peak_lower P n).trans hupper
  exact (not_lt_of_ge hpeak_le_poly) hpoly_lt_peak

lemma f_transcendental_entire
    {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀) :
    TranscendentalEntire (f P) := by
  exact ⟨f_differentiable P, f_not_polynomial P⟩

/-- Uniform bound on the imaginary axis.

This constant is independent of the point `z`; `P` is only a type/indexing
parameter here. -/
def imagAxisBound {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀) : ℝ :=
  ∑' n : ℕ, Real.exp (-(N n))

lemma imag_axis_bound
    {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀) {z : ℂ}
    (hz : z.re = 0) :
    ‖f P z‖ ≤ imagAxisBound P := by
  have hsumm_major : Summable (fun n : ℕ => Real.exp (-(N n))) := by
    refine Summable.of_nonneg_of_le
      (fun n : ℕ => Real.exp_nonneg _)
      (fun n : ℕ => ?_)
      Real.summable_exp_neg_nat
    show Real.exp (-(N n)) ≤ Real.exp (-(n : ℝ))
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    unfold N
    exact_mod_cast Nat.le_succ n
  have hterm_bound : ∀ n : ℕ, ‖term P n z‖ ≤ Real.exp (-(N n)) := by
    intro n
    have hterm_norm : ‖term P n z‖ = Real.exp (-(P.a n)) := by
      unfold term
      rw [Complex.norm_exp]
      congr 1
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        hz, mul_zero, zero_mul, sub_zero, add_zero]
    have hN_one : (1 : ℝ) ≤ N n := by
      unfold N
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hN_sq : N n ≤ (N n) ^ 2 := by
      calc
        N n = N n * 1 := by ring
        _ ≤ N n * N n :=
          mul_le_mul_of_nonneg_left hN_one (le_of_lt (N_pos n))
        _ = (N n) ^ 2 := by ring
    have hlam_nonneg : 0 ≤ P.lam n * N n :=
      mul_nonneg (le_of_lt (P.lam_pos n)) (le_of_lt (N_pos n))
    have hN_le_a : N n ≤ P.a n := by
      calc
        N n ≤ (N n) ^ 2 := hN_sq
        _ ≤ (N n) ^ 2 + P.lam n * N n := le_add_of_nonneg_right hlam_nonneg
        _ ≤ P.a n := P.a_large n
    rw [hterm_norm]
    exact Real.exp_le_exp.mpr (neg_le_neg hN_le_a)
  have hsumm_term_norm : Summable (fun n : ℕ => ‖term P n z‖) :=
    Summable.of_nonneg_of_le (fun n : ℕ => norm_nonneg _) hterm_bound hsumm_major
  calc
    ‖f P z‖ = ‖∑' n : ℕ, term P n z‖ := rfl
    _ ≤ ∑' n : ℕ, ‖term P n z‖ := norm_tsum_le_tsum_norm hsumm_term_norm
    _ ≤ ∑' n : ℕ, Real.exp (-(N n)) :=
      Summable.tsum_le_tsum hterm_bound hsumm_term_norm hsumm_major
    _ = imagAxisBound P := rfl

lemma Mc_tendsto_atTop
    {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀) :
    Tendsto (fun R : ℝ => Mc (f P) R) atTop atTop := by
  /-
  For any threshold `C`, choose `n` so large that `C ≤ 2^(n+9)`.
  The parameter estimates give

      2^(n+9) ≤ exp(P.X n)/2.

  The peak lower bound at `zPeak n`, followed by the defining closed-disk
  maximum at any larger radius `R ≥ r n`, gives `C ≤ Mc (f P) R`.
  This avoids needing a separate monotonicity argument for `Mc` here.
  -/
  rw [Filter.tendsto_atTop_atTop]
  intro C
  obtain ⟨n, hnC⟩ := exists_nat_gt C
  refine ⟨r n, ?_⟩
  intro R hR
  have hCpow : C ≤ (2 : ℝ) ^ (n + 9) := by
    have hCn : C ≤ (n : ℝ) := le_of_lt hnC
    have hnat_pow : (n : ℝ) ≤ (2 : ℝ) ^ (n + 9) := by
      have hnat : n ≤ 2 ^ (n + 9) := by
        have hle : n ≤ n + 9 := by omega
        have hlt : n + 9 < 2 ^ (n + 9) := (n + 9).lt_two_pow_self
        exact hle.trans hlt.le
      exact_mod_cast hnat
    exact hCn.trans hnat_pow
  have hpow_exp : (2 : ℝ) ^ (n + 9) ≤ Real.exp (P.X n) / 2 := by
    calc
      (2 : ℝ) ^ (n + 9) = 2 * (2 : ℝ) ^ (n + 8) := by
        rw [show n + 9 = n + 8 + 1 by omega, pow_succ]
        ring
      _ ≤ 2 * A Φ (P.X n) := by
        exact mul_le_mul_of_nonneg_left (P.A_large n) (by norm_num)
      _ ≤ 2 * (Real.exp (P.X n) / 4) := by
        exact mul_le_mul_of_nonneg_left (A_le_exp_quarter Φ (P.X n)) (by norm_num)
      _ = Real.exp (P.X n) / 2 := by
        ring
  have hzR : ‖zPeak n‖ ≤ R := by
    rw [norm_zPeak n]
    exact hR
  have hnorm_Mc : ‖f P (zPeak n)‖ ≤ Mc (f P) R :=
    norm_le_Mc (f P) (f_differentiable P).continuous hzR
  exact hCpow.trans (hpow_exp.trans ((f_peak_lower P n).trans hnorm_Mc))

lemma Phi_Mc_tendsto_atTop
    {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀)
    (hΦ_top : Tendsto Φ atTop atTop) :
    Tendsto (fun R : ℝ => Φ (Mc (f P) R)) atTop atTop := by
  -- Composition of `hΦ_top` with `Mc_tendsto_atTop P`.
  exact hΦ_top.comp (Mc_tendsto_atTop P)

lemma wrong_halfplane_ratio_small
    {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀)
    (T₀ : ℝ)
    (hx₀ : ∀ x : ℝ, x₀ ≤ x → T₀ ≤ Real.exp x / 2)
    (hΦ_mono : MonotoneOn Φ (Set.Ici T₀))
    (hΦ_pos : ∀ T : ℝ, T₀ ≤ T → 0 < Φ T)
    (n : ℕ) (z : ℂ)
    (hz : ‖z‖ = r n)
    (hwrong : eps n * z.re ≤ 0) :
    ‖f P z‖ / Φ (Mc (f P) (r n)) ≤ (1 / 2 : ℝ) ^ (n + 4) := by
  classical

  -- Abbreviate the comparison scale at the selected peak.
  let B : ℝ := A Φ (P.X n)
  have hB_large : (2 : ℝ) ^ (n + 8) ≤ B := by
    dsimp [B]
    exact P.A_large n
  have hB_pos : 0 < B :=
    lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℝ) < 2) (n + 8)) hB_large
  have hB_nonneg : 0 ≤ B := le_of_lt hB_pos

  -- On the wrong half-plane, the diagonal term is at most `1`.
  have hmain_le_one : ‖term P n z‖ ≤ 1 := by
    have hterm_norm :
        ‖term P n z‖ =
          Real.exp (-(P.a n) + (eps n * P.lam n) * z.re) := by
      unfold term
      rw [Complex.norm_exp]
      congr 1
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        mul_zero, sub_zero, zero_mul, add_zero]
    rw [hterm_norm]
    have hsigned : (eps n * P.lam n) * z.re ≤ 0 := by
      calc
        (eps n * P.lam n) * z.re = P.lam n * (eps n * z.re) := by ring
        _ ≤ P.lam n * 0 :=
          mul_le_mul_of_nonneg_left hwrong (le_of_lt (P.lam_pos n))
        _ = 0 := by ring
    have ha_nonneg : 0 ≤ P.a n := by
      have hN_nonneg : 0 ≤ N n := le_of_lt (N_pos n)
      have hlamN_nonneg : 0 ≤ P.lam n * N n :=
        mul_nonneg (le_of_lt (P.lam_pos n)) hN_nonneg
      have hNsq_nonneg : 0 ≤ (N n) ^ 2 := sq_nonneg (N n)
      nlinarith [P.a_large n, hlamN_nonneg, hNsq_nonneg]
    calc
      Real.exp (-(P.a n) + (eps n * P.lam n) * z.re)
          ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith)
      _ = 1 := Real.exp_zero

  -- A summable majorant for every term on this circle: one singleton contribution
  -- for the diagonal term, plus a full geometric series for the off-diagonal terms.
  let geom : ℕ → ℝ :=
    fun m => ((1 / 2 : ℝ) ^ (n + 10) * B) * (1 / 2 : ℝ) ^ m
  let G : ℕ → ℝ := fun m => (if m = n then 1 else 0) + geom m

  have hterm_bound : ∀ m : ℕ, ‖term P m z‖ ≤ G m := by
    intro m
    by_cases hmn : m = n
    · subst m
      have hgeom_nonneg : 0 ≤ geom n := by
        dsimp [geom]
        exact mul_nonneg
          (mul_nonneg (pow_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) (n + 10)) hB_nonneg)
          (pow_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) n)
      calc
        ‖term P n z‖ ≤ 1 := hmain_le_one
        _ ≤ G n := by
          dsimp [G]
          simp
          linarith
    · have hoff :
          ‖term P m z‖ ≤ (1 / 2 : ℝ) ^ (m + n + 10) * B := by
        calc
          ‖term P m z‖
              ≤ Real.exp (-(P.a m) + P.lam m * ‖z‖) :=
                term_norm_le_exp_norm P m z
          _ = Real.exp (-(P.a m) + P.lam m * r n) := by rw [hz]
          _ ≤ (1 / 2 : ℝ) ^ (m + n + 10) * A Φ (P.X n) :=
                P.offdiag m n hmn
          _ = (1 / 2 : ℝ) ^ (m + n + 10) * B := by dsimp [B]
      have hgeom_eq :
          (1 / 2 : ℝ) ^ (m + n + 10) * B = geom m := by
        dsimp [geom]
        have hadd : m + n + 10 = m + (n + 10) := by omega
        rw [hadd, pow_add]
        ring
      calc
        ‖term P m z‖ ≤ (1 / 2 : ℝ) ^ (m + n + 10) * B := hoff
        _ = geom m := hgeom_eq
        _ ≤ G m := by
          dsimp [G]
          simp [hmn]

  have hhalf_summable : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ m) :=
    summable_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)
  have hhalf_tsum : (∑' m : ℕ, (1 / 2 : ℝ) ^ m) = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)]
    norm_num
  have hhalf_hasSum : HasSum (fun m : ℕ => (1 / 2 : ℝ) ^ m) 2 := by
    convert hhalf_summable.hasSum using 1
    exact hhalf_tsum.symm
  have hgeom_hasSum :
      HasSum geom (((1 / 2 : ℝ) ^ (n + 10) * B) * 2) := by
    simpa [geom] using
      hhalf_hasSum.mul_left (((1 / 2 : ℝ) ^ (n + 10) * B))
  have hsingle_hasSum :
      HasSum (fun m : ℕ => if m = n then (1 : ℝ) else 0) 1 := by
    simpa using (hasSum_ite_eq n (1 : ℝ))
  have hG_hasSum :
      HasSum G (1 + (((1 / 2 : ℝ) ^ (n + 10) * B) * 2)) := by
    simpa [G] using hsingle_hasSum.add hgeom_hasSum

  have hf_upper :
      ‖f P z‖ ≤ 1 + (((1 / 2 : ℝ) ^ (n + 10) * B) * 2) := by
    unfold f
    exact tsum_of_norm_bounded (f := fun m : ℕ => term P m z)
      (g := G) hG_hasSum hterm_bound

  -- Absorb the singleton contribution into the large value of `A Φ (P.X n)`.
  have hone_absorb : 1 ≤ (1 / 2 : ℝ) ^ (n + 8) * B := by
    calc
      1 = (1 / 2 : ℝ) ^ (n + 8) * (2 : ℝ) ^ (n + 8) := by
        rw [← mul_pow]
        norm_num
      _ ≤ (1 / 2 : ℝ) ^ (n + 8) * B :=
        mul_le_mul_of_nonneg_left hB_large
          (pow_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) (n + 8))

  have htail_eq :
      (((1 / 2 : ℝ) ^ (n + 10) * B) * 2) =
        (1 / 2 : ℝ) ^ (n + 9) * B := by
    have hsucc : n + 10 = (n + 9) + 1 := by omega
    rw [hsucc, pow_succ]
    ring

  have hpow_sum :
      (1 / 2 : ℝ) ^ (n + 8) + (1 / 2 : ℝ) ^ (n + 9)
        ≤ (1 / 2 : ℝ) ^ (n + 4) := by
    have hq_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
    have hq_le_one : (1 / 2 : ℝ) ≤ 1 := by norm_num
    have hp8 : (1 / 2 : ℝ) ^ (n + 8) ≤ (1 / 2 : ℝ) ^ (n + 5) :=
      pow_le_pow_of_le_one hq_nonneg hq_le_one (by omega)
    have hp9 : (1 / 2 : ℝ) ^ (n + 9) ≤ (1 / 2 : ℝ) ^ (n + 5) :=
      pow_le_pow_of_le_one hq_nonneg hq_le_one (by omega)
    have htwice : (1 / 2 : ℝ) ^ (n + 4) = 2 * (1 / 2 : ℝ) ^ (n + 5) := by
      have hsucc : n + 5 = (n + 4) + 1 := by omega
      rw [hsucc, pow_succ]
      ring
    nlinarith
  have hpow_mul :
      ((1 / 2 : ℝ) ^ (n + 8) + (1 / 2 : ℝ) ^ (n + 9)) * B
        ≤ (1 / 2 : ℝ) ^ (n + 4) * B :=
    mul_le_mul_of_nonneg_right hpow_sum hB_nonneg

  have hf_le_A : ‖f P z‖ ≤ (1 / 2 : ℝ) ^ (n + 4) * B := by
    calc
      ‖f P z‖ ≤ 1 + (((1 / 2 : ℝ) ^ (n + 10) * B) * 2) := hf_upper
      _ = 1 + (1 / 2 : ℝ) ^ (n + 9) * B := by rw [htail_eq]
      _ ≤ (1 / 2 : ℝ) ^ (n + 8) * B + (1 / 2 : ℝ) ^ (n + 9) * B :=
        add_le_add hone_absorb le_rfl
      _ = ((1 / 2 : ℝ) ^ (n + 8) + (1 / 2 : ℝ) ^ (n + 9)) * B := by ring
      _ ≤ (1 / 2 : ℝ) ^ (n + 4) * B := hpow_mul

  -- Compare the denominator with `A Φ (P.X n)`.
  have hbase_T₀ : T₀ ≤ Real.exp (P.X n) / 2 :=
    hx₀ (P.X n) (P.X_ge_x0 n)
  have hMc_lower : Real.exp (P.X n) / 2 ≤ Mc (f P) (r n) :=
    Mc_peak_lower P n
  have hMc_ge_T₀ : T₀ ≤ Mc (f P) (r n) := hbase_T₀.trans hMc_lower
  have hPhi_mono :
      Φ (Real.exp (P.X n) / 2) ≤ Φ (Mc (f P) (r n)) :=
    hΦ_mono hbase_T₀ hMc_ge_T₀ hMc_lower
  have hA_le_den : B ≤ Φ (Mc (f P) (r n)) := by
    dsimp [B]
    exact (A_le_phi Φ (P.X n)).trans hPhi_mono
  have hden_pos : 0 < Φ (Mc (f P) (r n)) :=
    hΦ_pos (Mc (f P) (r n)) hMc_ge_T₀

  have hf_le_den :
      ‖f P z‖ ≤ (1 / 2 : ℝ) ^ (n + 4) * Φ (Mc (f P) (r n)) :=
    hf_le_A.trans <|
      mul_le_mul_of_nonneg_left hA_le_den
        (pow_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) (n + 4))

  rw [div_le_iff₀ hden_pos]
  exact hf_le_den

lemma imag_axis_ratio_eventually
    {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀)
    (T₀ : ℝ)
    (hΦ_pos : ∀ T : ℝ, T₀ ≤ T → 0 < Φ T)
    (hΦ_top : Tendsto Φ atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ,
      z.re = 0 → R ≤ ‖z‖ →
        ‖f P z‖ / Φ (Mc (f P) ‖z‖) ≤ ε := by
  intro ε hε
  -- The denominator tends to `∞`; make it at least both `1` and
  -- `imagAxisBound P / ε`.  The lower bound by `1` gives positivity.
  have hden_top : Tendsto (fun R : ℝ => Φ (Mc (f P) R)) atTop atTop :=
    Phi_Mc_tendsto_atTop P hΦ_top
  rw [Filter.tendsto_atTop_atTop] at hden_top
  obtain ⟨R, hR⟩ := hden_top (max (1 : ℝ) (imagAxisBound P / ε))
  refine ⟨R, ?_⟩
  intro z hz_re hzR
  let D : ℝ := Φ (Mc (f P) ‖z‖)
  have hD_ge : max (1 : ℝ) (imagAxisBound P / ε) ≤ D := by
    simpa [D] using hR ‖z‖ hzR
  have hD_pos : 0 < D := by
    have h1D : (1 : ℝ) ≤ D :=
      (le_max_left (1 : ℝ) (imagAxisBound P / ε)).trans hD_ge
    exact lt_of_lt_of_le zero_lt_one h1D
  have hnum_bound : ‖f P z‖ ≤ imagAxisBound P :=
    imag_axis_bound P hz_re
  have hB_div : imagAxisBound P / ε ≤ D :=
    (le_max_right (1 : ℝ) (imagAxisBound P / ε)).trans hD_ge
  have hB_mul : imagAxisBound P ≤ D * ε := by
    have hmul := mul_le_mul_of_nonneg_right hB_div (le_of_lt hε)
    rwa [div_mul_cancel₀ (imagAxisBound P) (ne_of_gt hε)] at hmul
  have hnum_mul : ‖f P z‖ ≤ ε * D := by
    calc
      ‖f P z‖ ≤ imagAxisBound P := hnum_bound
      _ ≤ D * ε := hB_mul
      _ = ε * D := by ring
  change ‖f P z‖ / D ≤ ε
  rw [div_le_iff₀ hD_pos]
  exact hnum_mul

/-- Practical path formulation: arbitrary late small values along every path to infinity. -/
def FrequentlySmall
    (Φ : ℝ → ℝ) (M : (ℂ → ℂ) → ℝ → ℝ) (g : ℂ → ℂ) : Prop :=
  ∀ γ : ℝ → ℂ,
    Continuous γ →
    Tendsto (fun t : ℝ => ‖γ t‖) atTop atTop →
    ∀ ε : ℝ, 0 < ε → ∀ T : ℝ,
      ∃ t : ℝ, T ≤ t ∧ ‖g (γ t)‖ / Φ (M g ‖γ t‖) ≤ ε

lemma path_crossing_argument
    {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀)
    (T₀ : ℝ)
    (hx₀ : ∀ x : ℝ, x₀ ≤ x → T₀ ≤ Real.exp x / 2)
    (hΦ_mono : MonotoneOn Φ (Set.Ici T₀))
    (hΦ_pos : ∀ T : ℝ, T₀ ≤ T → 0 < Φ T)
    (hΦ_top : Tendsto Φ atTop atTop)
    (γ : ℝ → ℂ)
    (hγ_cont : Continuous γ)
    (hγ_inf : Tendsto (fun t : ℝ => ‖γ t‖) atTop atTop)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧ ‖f P (γ t)‖ / Φ (Mc (f P) ‖γ t‖) ≤ ε := by
  /-
  This is the formal version of the first-hitting-time argument in the note.
  We avoid defining first hitting times.  Instead, after a sufficiently late
  time `T₁`, choose two consecutive construction radii `r n`, `r (n+1)` crossed
  by the continuous function `t ↦ ‖γ t‖`.  At the two crossing points either one
  lies in the wrong half-plane, or the real part crosses the imaginary axis
  between them.
  -/
  obtain ⟨Rim, hRim⟩ := imag_axis_ratio_eventually P T₀ hΦ_pos hΦ_top ε hε

  -- After a sufficiently late time the path is large enough for the imaginary
  -- axis estimate, and we also stay later than the prescribed lower time `T`.
  have hlarge_eventually : ∀ᶠ t in atTop, Rim ≤ ‖γ t‖ :=
    hγ_inf.eventually_ge_atTop Rim
  obtain ⟨S, hS⟩ := (eventually_atTop.1 hlarge_eventually)
  let T₁ : ℝ := max T S
  have hT_le_T₁ : T ≤ T₁ := by
    exact le_max_left T S
  have hS_le_T₁ : S ≤ T₁ := by
    exact le_max_right T S
  have hlarge_after_T₁ : ∀ t : ℝ, T₁ ≤ t → Rim ≤ ‖γ t‖ := by
    intro t ht
    exact hS t (le_trans hS_le_T₁ ht)

  -- Pick `n` so that the wrong-half-plane bound is below `ε`, and so that
  -- the circle `‖z‖ = r n` is already beyond the current point `γ T₁`.
  obtain ⟨nε, hnε⟩ :=
    exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨nB, hnB⟩ := exists_nat_gt (‖γ T₁‖)
  let n : ℕ := max nε nB
  have hnε_le_n : nε ≤ n := by
    exact Nat.le_max_left nε nB
  have hnB_le_n : nB ≤ n := by
    exact Nat.le_max_right nε nB
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hhalf_le_one : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hpow_n : (1 / 2 : ℝ) ^ (n + 4) ≤ ε := by
    have hpow_le : (1 / 2 : ℝ) ^ (n + 4) ≤ (1 / 2 : ℝ) ^ nε := by
      exact pow_le_pow_of_le_one hhalf_nonneg hhalf_le_one (by omega)
    exact hpow_le.trans (le_of_lt hnε)
  have hpow_succ : (1 / 2 : ℝ) ^ (n + 1 + 4) ≤ ε := by
    have hpow_le : (1 / 2 : ℝ) ^ (n + 1 + 4) ≤ (1 / 2 : ℝ) ^ (n + 4) := by
      exact pow_le_pow_of_le_one hhalf_nonneg hhalf_le_one (by omega)
    exact hpow_le.trans hpow_n
  have hT₁_norm_lt_rn : ‖γ T₁‖ < r n := by
    have hlt_nat : ‖γ T₁‖ < (n : ℝ) := by
      exact lt_of_lt_of_le hnB (by exact_mod_cast hnB_le_n)
    unfold r
    exact lt_of_lt_of_le hlt_nat (by exact_mod_cast (by omega : n ≤ n + 2))

  -- Choose a later point whose norm is beyond the next construction radius.
  obtain ⟨u, hT₁_le_u, hu_norm⟩ :=
    exists_le_of_tendsto_atTop hγ_inf T₁ (r (n + 1))
  have hrn_le_u_norm : r n ≤ ‖γ u‖ := by
    exact (le_of_lt (r_strictMono (Nat.lt_succ_self n))).trans hu_norm

  -- First crossing: `‖γ t₀‖ = r n`.
  have hcont_norm_Icc : ContinuousOn (fun t : ℝ => ‖γ t‖) (Set.Icc T₁ u) := by
    exact (continuous_norm.comp hγ_cont).continuousOn
  have hrn_mem : r n ∈ Set.Icc (‖γ T₁‖) (‖γ u‖) := by
    exact ⟨le_of_lt hT₁_norm_lt_rn, hrn_le_u_norm⟩
  obtain ⟨t₀, ht₀_Icc, ht₀_norm⟩ :=
    intermediate_value_Icc hT₁_le_u hcont_norm_Icc hrn_mem

  -- Second crossing: `‖γ t₁‖ = r (n+1)`.
  have ht₀_le_u : t₀ ≤ u := ht₀_Icc.2
  have hrn_lt_rsucc : r n < r (n + 1) :=
    r_strictMono (Nat.lt_succ_self n)
  have hcont_norm_Icc₂ : ContinuousOn (fun t : ℝ => ‖γ t‖) (Set.Icc t₀ u) := by
    exact (continuous_norm.comp hγ_cont).continuousOn
  have hrsucc_mem : r (n + 1) ∈ Set.Icc (‖γ t₀‖) (‖γ u‖) := by
    refine ⟨?_, hu_norm⟩
    simpa [ht₀_norm] using le_of_lt hrn_lt_rsucc
  obtain ⟨t₁, ht₁_Icc, ht₁_norm⟩ :=
    intermediate_value_Icc ht₀_le_u hcont_norm_Icc₂ hrsucc_mem

  -- If either crossing point lies in the wrong half-plane, the prepared
  -- estimate immediately gives a small value.
  by_cases hwrong₀ : eps n * (γ t₀).re ≤ 0
  · refine ⟨t₀, ?_, ?_⟩
    · exact hT_le_T₁.trans ht₀_Icc.1
    · have hsmall :=
        wrong_halfplane_ratio_small P T₀ hx₀ hΦ_mono hΦ_pos n (γ t₀) ht₀_norm hwrong₀
      have hsmallε :
          ‖f P (γ t₀)‖ / Φ (Mc (f P) (r n)) ≤ ε :=
        hsmall.trans hpow_n
      simpa [ht₀_norm] using hsmallε
  · by_cases hwrong₁ : eps (n + 1) * (γ t₁).re ≤ 0
    · refine ⟨t₁, ?_, ?_⟩
      · exact hT_le_T₁.trans (ht₀_Icc.1.trans ht₁_Icc.1)
      · have hsmall :=
          wrong_halfplane_ratio_small P T₀ hx₀ hΦ_mono hΦ_pos (n + 1) (γ t₁)
            ht₁_norm hwrong₁
        have hsmallε :
            ‖f P (γ t₁)‖ / Φ (Mc (f P) (r (n + 1))) ≤ ε :=
          hsmall.trans hpow_succ
        simpa [ht₁_norm] using hsmallε
    · -- Otherwise the signed real parts have opposite signs, so the path
      -- crosses the imaginary axis between `t₀` and `t₁`.
      have hpos₀ : 0 < eps n * (γ t₀).re := lt_of_not_ge hwrong₀
      have hpos₁ : 0 < eps (n + 1) * (γ t₁).re := lt_of_not_ge hwrong₁
      have hneg₁ : eps n * (γ t₁).re < 0 := by
        have htmp : 0 < -(eps n * (γ t₁).re) := by
          simpa [eps_succ, neg_mul] using hpos₁
        exact neg_pos.mp htmp
      have ht₀_le_t₁ : t₀ ≤ t₁ := ht₁_Icc.1
      have hcont_signed_re :
          ContinuousOn (fun t : ℝ => eps n * (γ t).re) (Set.Icc t₀ t₁) := by
        exact ((continuous_const : Continuous fun _ : ℝ => eps n).mul
          (Complex.continuous_re.comp hγ_cont)).continuousOn
      have hzero_mem :
          (0 : ℝ) ∈ Set.Icc (eps n * (γ t₁).re) (eps n * (γ t₀).re) := by
        exact ⟨le_of_lt hneg₁, le_of_lt hpos₀⟩
      obtain ⟨s, hs_Icc, hs_signed_re⟩ :=
        intermediate_value_Icc' ht₀_le_t₁ hcont_signed_re hzero_mem
      have hs_re : (γ s).re = 0 := by
        have hmul : eps n * (γ s).re = 0 := by
          simpa using hs_signed_re
        exact (mul_eq_zero.mp hmul).resolve_left (eps_ne_zero n)
      refine ⟨s, ?_, ?_⟩
      · exact hT_le_T₁.trans (ht₀_Icc.1.trans hs_Icc.1)
      · have hs_large : Rim ≤ ‖γ s‖ :=
          hlarge_after_T₁ s (ht₀_Icc.1.trans hs_Icc.1)
        exact hRim (γ s) hs_re hs_large

lemma frequentlySmall_paths
    {Φ : ℝ → ℝ} {x₀ : ℝ} (P : Params Φ x₀)
    (T₀ : ℝ)
    (hx₀ : ∀ x : ℝ, x₀ ≤ x → T₀ ≤ Real.exp x / 2)
    (hΦ_mono : MonotoneOn Φ (Set.Ici T₀))
    (hΦ_pos : ∀ T : ℝ, T₀ ≤ T → 0 < Φ T)
    (hΦ_top : Tendsto Φ atTop atTop) :
    FrequentlySmall Φ Mc (f P) := by
  intro γ hγ_cont hγ_inf ε hε T
  exact path_crossing_argument P T₀ hx₀ hΦ_mono hΦ_pos hΦ_top γ hγ_cont hγ_inf ε hε T

/-- Main theorem in the closed-disk maximum formulation. -/
theorem comparison_negative_closedDisk
    (Φ : ℝ → ℝ) (T₀ : ℝ)
    (hΦ_mono : MonotoneOn Φ (Set.Ici T₀))
    (hΦ_pos : ∀ T : ℝ, T₀ ≤ T → 0 < Φ T)
    (hΦ_top : Tendsto Φ atTop atTop) :
    ∃ g : ℂ → ℂ,
      TranscendentalEntire g ∧ FrequentlySmall Φ Mc g := by
  obtain ⟨x₀, _hx₀_pos, hx₀⟩ := exists_x0 T₀
  have hA : Tendsto (A Φ) atTop atTop :=
    tendsto_A_atTop Φ T₀ x₀ hx₀ hΦ_top
  obtain ⟨P, _⟩ := exists_params Φ x₀ hA
  refine ⟨f P, ?_, ?_⟩
  · exact f_transcendental_entire P
  · exact frequentlySmall_paths P T₀ hx₀ hΦ_mono hΦ_pos hΦ_top

/-!
## Bridge to the circle maximum

The paper defines `M_f(r) = max_{|z|=r} |f z|`.  The construction above first
proves the estimates for the closed-disk supremum `Mc`; the maximum-modulus
principle then identifies this with the circle supremum `Ms` for positive
radii.
-/

lemma Mc_eq_Ms_of_transcendental
    {g : ℂ → ℂ}
    (hg : TranscendentalEntire g)
    {R : ℝ} (hR : 0 < R) :
    Mc g R = Ms g R := by
  /-
  Maximum modulus principle on the closed disk.

  We use the mathlib form `Complex.exists_mem_frontier_isMaxOn_norm`: for a
  bounded nonempty open ball and a function differentiable on it and continuous
  on its closure, there is a boundary point at which `‖g‖` is maximal on the
  closure.  This is enough to identify the two `sSup` definitions.  The
  non-polynomial part of `hg` is not needed for this standard maximum-modulus
  bridge.
  -/
  let U : Set ℂ := Metric.ball (0 : ℂ) R
  have hU_bdd : Bornology.IsBounded U := by
    simpa [U] using (Metric.isBounded_ball : Bornology.IsBounded (Metric.ball (0 : ℂ) R))
  have hU_nonempty : U.Nonempty := by
    simpa [U] using (Metric.nonempty_ball.mpr hR : (Metric.ball (0 : ℂ) R).Nonempty)
  have hdiff : DiffContOnCl ℂ g U := by
    exact hg.1.diffContOnCl
  obtain ⟨z₀, hz₀_frontier, hz₀_max⟩ :=
    Complex.exists_mem_frontier_isMaxOn_norm
      (f := g) (U := U) hU_bdd hU_nonempty hdiff
  have hz₀_sphere : z₀ ∈ Metric.sphere (0 : ℂ) R := by
    simpa [U, frontier_ball (0 : ℂ) hR.ne'] using hz₀_frontier
  have hz₀_norm : ‖z₀‖ = R := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hz₀_sphere
  have hle_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ R) : ‖g z‖ ≤ ‖g z₀‖ := by
    apply hz₀_max
    change z ∈ closure (Metric.ball (0 : ℂ) R)
    rw [closure_ball (0 : ℂ) hR.ne']
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hMc_greatest :
      IsGreatest { y : ℝ | ∃ z : ℂ, ‖z‖ ≤ R ∧ y = ‖g z‖ } ‖g z₀‖ := by
    constructor
    · exact ⟨z₀, hz₀_norm.le, rfl⟩
    · intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      exact hle_of_norm_le hz
  have hMs_greatest :
      IsGreatest { y : ℝ | ∃ z : ℂ, ‖z‖ = R ∧ y = ‖g z‖ } ‖g z₀‖ := by
    constructor
    · exact ⟨z₀, hz₀_norm, rfl⟩
    · intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      exact hle_of_norm_le hz.le
  calc
    Mc g R = ‖g z₀‖ := by
      unfold Mc
      exact IsGreatest.csSup_eq hMc_greatest
    _ = Ms g R := by
      unfold Ms
      exact (IsGreatest.csSup_eq hMs_greatest).symm

lemma frequentlySmall_Mc_to_Ms
    {Φ : ℝ → ℝ} {g : ℂ → ℂ}
    (hg : TranscendentalEntire g)
    (hsmall : FrequentlySmall Φ Mc g) :
    FrequentlySmall Φ Ms g := by
  intro γ hγ_cont hγ_inf ε hε T
  have hlarge_eventually : ∀ᶠ t in atTop, (1 : ℝ) ≤ ‖γ t‖ :=
    hγ_inf.eventually (Filter.eventually_ge_atTop (1 : ℝ))
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp hlarge_eventually
  obtain ⟨t, ht, hratio⟩ := hsmall γ hγ_cont hγ_inf ε hε (max T T₁)
  have hTt : T ≤ t := le_trans (le_max_left T T₁) ht
  have hT₁t : T₁ ≤ t := le_trans (le_max_right T T₁) ht
  have hRpos : 0 < ‖γ t‖ := lt_of_lt_of_le zero_lt_one (hT₁ t hT₁t)
  refine ⟨t, hTt, ?_⟩
  have hEq : Mc g ‖γ t‖ = Ms g ‖γ t‖ :=
    Mc_eq_Ms_of_transcendental hg hRpos
  rwa [← hEq]

/-- Main theorem in the epsilon/frequently-small circle-maximum formulation
corresponding to the TeX theorem. -/
theorem comparison_negative_sphere
    (Φ : ℝ → ℝ) (T₀ : ℝ)
    (hΦ_mono : MonotoneOn Φ (Set.Ici T₀))
    (hΦ_pos : ∀ T : ℝ, T₀ ≤ T → 0 < Φ T)
    (hΦ_top : Tendsto Φ atTop atTop) :
    ∃ g : ℂ → ℂ,
      TranscendentalEntire g ∧ FrequentlySmall Φ Ms g := by
  obtain ⟨g, hg, hsmall⟩ :=
    comparison_negative_closedDisk Φ T₀ hΦ_mono hΦ_pos hΦ_top
  exact ⟨g, hg, frequentlySmall_Mc_to_Ms hg hsmall⟩

#print axioms comparison_negative_sphere
-- 'Erdos514.comparison_negative_sphere' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos514

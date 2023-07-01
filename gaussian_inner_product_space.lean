import analysis.calculus.cont_diff_def
import analysis.calculus.mean_value
import analysis.normed_space.finite_dimension
import data.nat.choose.cast
import algebra.geom_sum
import data.complex.basic
import data.nat.choose.sum
import data.complex.exponential
import analysis.normed_space.exponential
import analysis.special_functions.log.basic
import data.polynomial.basic
import data.polynomial.eval
import analysis.schwartz_space
import analysis.normed_space.exponential
import tactic
import topology.basic
import analysis.special_functions.log.base
import analysis.calculus.iterated_deriv
import analysis.special_functions.exp_deriv
import number_theory.dioph
import analysis.complex.real_deriv
import analysis.special_functions.gaussian
import analysis.inner_product_space.calculus
import analysis.calculus.cont_diff


open_locale classical big_operators nnreal nat

local notation `∞` := (⊤ : ℕ∞)

universes u v w uD uE uF uG

open set fin filter function
open_locale topology

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{D : Type uD} [normed_add_comm_group D] [normed_space 𝕜 D]
{E : Type uE} [normed_add_comm_group E] [normed_space 𝕜 E]
{F : Type uF} [normed_add_comm_group F] [normed_space 𝕜 F]
{G : Type uG} [normed_add_comm_group G] [normed_space 𝕜 G]
{X : Type*} [normed_add_comm_group X] [normed_space 𝕜 X]
{s s₁ t u : set E} {f f₁ : E → F} {g : F → G} {x x₀ : E} {c : F}
{b : E × F → G} {m n : ℕ∞} {p : E → formal_multilinear_series 𝕜 E F}


/-- If the derivatives of `g` at `f x` are bounded by `C`, and the `i`-th derivative
of `f` at `x` is bounded by `D^i` for all `1 ≤ i ≤ n`, then the `n`-th derivative
of `g ∘ f` is bounded by `n! * C * D^n`. -/
lemma norm_iterated_fderiv_comp_le
  {g : F → G} {f : E → F} {n : ℕ} {N : ℕ∞}
  (hg : cont_diff 𝕜 N g) (hf : cont_diff 𝕜 N f) (hn : (n : ℕ∞) ≤ N) (x : E)
  {C : ℝ} {D : ℝ} (hC : ∀ i, i ≤ n → ‖iterated_fderiv 𝕜 i g (f x)‖ ≤ C)
  (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iterated_fderiv 𝕜 i f x‖ ≤ D^i) :
  ‖iterated_fderiv 𝕜 n (g ∘ f) x‖ ≤ n! * C * D^n :=
begin 
  simp_rw [← iterated_fderiv_within_univ] at ⊢ hC hD, ℝ
  exact norm_iterated_fderiv_within_comp_le hg.cont_diff_on hf.cont_diff_on hn unique_diff_on_univ
    unique_diff_on_univ (maps_to_univ _ _) (mem_univ x) hC hD,
end

lemma norm_iterated_fderiv_comp_le'
  (g : F → G) (f : E → F) (n : ℕ) (N : ℕ∞)
  (hg : cont_diff 𝕜 N g) (hf : cont_diff 𝕜 N f) (hn : (n : ℕ∞) ≤ N) (x : E)
  (C : ℝ) (D : ℝ) (hC : ∀ i, i ≤ n → ‖iterated_fderiv 𝕜 i g (f x)‖ ≤ C)
  (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iterated_fderiv 𝕜 i f x‖ ≤ D^i) :
  ‖iterated_fderiv 𝕜 n (g ∘ f) x‖ ≤ n! * C * D^n :=
begin
  refine norm_iterated_fderiv_comp_le hg hf hn x hC hD,
end


lemma continuous_linear_map.norm_iterated_fderiv_le_of_bilinear
  (B : E →L[𝕜] F →L[𝕜] G) {f : D → E} {g : D → F} {N : ℕ∞}
  (hf : cont_diff 𝕜 N f) (hg : cont_diff 𝕜 N g) (x : D)
  {n : ℕ} (hn : (n : ℕ∞) ≤ N) :
  ‖iterated_fderiv 𝕜 n (λ y, B (f y) (g y)) x‖
    ≤ ‖B‖ * ∑ i in finset.range (n+1), (n.choose i : ℝ)
      * ‖iterated_fderiv 𝕜 i f x‖ * ‖iterated_fderiv 𝕜 (n-i) g x‖ :=
begin
  sorry,
end


local notation `abs'` := has_abs.abs
open is_absolute_value
open_locale classical big_operators nat complex_conjugate

section
open real is_absolute_value finset
open polynomial
open set
open set filter
open schwartz_map
open_locale classical big_operators nat complex_conjugate
open real is_absolute_value finset
open finset
open cau_seq
open complex
open real

noncomputable theory

namespace real

/-- Orignial Proof from Mathlib where inspiration is taken from.
    The name is changed to contain the word original to not cause an error in the file --/
lemma add_one_le_exp_of_nonneg_original {x : ℝ} (hx : 0 ≤ x) : x + 1 ≤ exp x :=
calc x + 1 ≤ lim (⟨(λ n : ℕ, ((exp' x) n).re), is_cau_seq_re (exp' x)⟩ : cau_seq ℝ has_abs.abs) :
  le_lim (cau_seq.le_of_exists ⟨3,
    λ j hj, show x + (1 : ℝ) ≤ (∑ m in range j, (x ^ m / m! : ℂ)).re,
      from have h₁ : (((λ m : ℕ, (x ^ m / m! : ℂ)) ∘ nat.succ) 0).re = x, by rw [function.comp_app, pow_one, nat.factorial_one, algebra_map.coe_one, div_one, of_real_re],
      have h₂ : ((x : ℂ) ^ 0 / 0!).re = 1, by simp,
      begin
        rw [← tsub_add_cancel_of_le hj, sum_range_succ', sum_range_succ',
          add_re, add_re, h₁, h₂, add_assoc,
          ← coe_re_add_group_hom, (re_add_group_hom).map_sum, coe_re_add_group_hom ],
        refine le_add_of_nonneg_of_le (sum_nonneg (λ m hm, _)) le_rfl,
        rw [← of_real_pow, ← of_real_nat_cast, ← of_real_div, of_real_re],
        exact div_nonneg (pow_nonneg hx _) (nat.cast_nonneg _),
      end⟩)
... = exp x : by rw [exp, complex.exp, ← cau_seq_re, lim_re]


namespace my_work

open is_absolute_value
open_locale classical big_operators nat complex_conjugate
open real is_absolute_value finset
open is_absolute_value

variables {E' : Type*}  [normed_add_comm_group E']  [inner_product_space ℝ E']
 
lemma pow_div_factorial_le_exp_sum_pow_div_factorial {x : ℝ} {n : ℕ} (hx : 0 ≤ x) : 
x^n / n! ≤ (∑ (j : ℕ) in range n.succ, (x ^ j / j!: ℂ)).re:=
begin
  have h : ((↑x : ℂ) ^n/ ↑n!).re = x ^ n / n!,  by  rw [← of_real_pow, ← of_real_nat_cast, ← of_real_div, of_real_re],
  rw [sum_range_succ, add_re, h,← coe_re_add_group_hom, (re_add_group_hom).map_sum, coe_re_add_group_hom ],
  refine le_add_of_nonneg_of_le (sum_nonneg (λ m hm, _)) le_rfl,
  rw [← of_real_pow, ← of_real_nat_cast, ← of_real_div, of_real_re],
  exact div_nonneg (pow_nonneg hx _) (nat.cast_nonneg _),
end


lemma zero_le_sum_pow_div_factorial {x : ℝ} {n s: ℕ} (hx : 0 ≤ x) : 
(0 : ℝ) ≤ (∑ (j : ℕ) in range s, (↑x : ℂ) ^ (n.succ + j) / ↑(n.succ + j)!).re:=
begin
  rw [← coe_re_add_group_hom, (re_add_group_hom).map_sum, coe_re_add_group_hom, ←add_zero (finset.sum _)],
  refine le_add_of_nonneg_of_le (sum_nonneg (λ m hm, _)) le_rfl,
  rw [← of_real_pow, ← of_real_nat_cast, ← of_real_div, of_real_re],
  exact div_nonneg (pow_nonneg hx _) (nat.cast_nonneg _),
end


lemma m_ge_n_then_pow_div_factorial_le_exp_nonneg {x : ℝ} {n m : ℕ} (hx : 0 ≤ x) : 
m≥n.succ →  (x ^ (n) / (n)!) ≤ (∑ i in range m, (x ^ i / i! : ℂ)).re:=
begin
  intro hm,
  set s:= m-n.succ with hs,
  have h₁: m=n.succ+s, by {zify at hs, zify, linarith,},
  rw [h₁, finset.sum_range_add,add_re],
  refine le_add_of_le_of_nonneg _ _,
  refine pow_div_factorial_le_exp_sum_pow_div_factorial hx,
  refine zero_le_sum_pow_div_factorial hx,
end


lemma pow_div_factorial_le_exp_nonneg {x : ℝ} {n : ℕ} (hx : 0 ≤ x) : 
x ^ (n) / (n)! ≤ (complex.exp x).re :=
calc x ^ (n) / (n)! ≤ lim (⟨(λ n : ℕ, ((exp' x) n).re), is_cau_seq_re (exp' x)⟩ : cau_seq ℝ has_abs.abs) :
  le_lim (cau_seq.le_of_exists ⟨n.succ,
    λ m hm, show  x ^ (n) / (n)! ≤ (∑ i in range m, (x ^ i / i! : ℂ)).re,
      from have h₁ : m≥n.succ →  x ^ (n) / (n)! ≤ (∑ i in range m, (x ^ i / i! : ℂ)).re, by exact m_ge_n_then_pow_div_factorial_le_exp_nonneg hx,
      begin
        refine h₁ hm,
      end⟩)
... = exp x : by rw [exp, complex.exp, ← cau_seq_re, lim_re]


-- Credit to Moritz Doll
lemma complex.differentiable_at_coe {f : ℝ → ℝ} {x : ℝ} (hf : differentiable_at ℝ f x) :
differentiable_at ℝ (λ y, (f y : ℂ)) x :=
begin
  apply complex.of_real_clm.differentiable_at.comp _ hf,
end


lemma pow_div_factorial_le_abs_exp_nonneg {x : ℝ} {n : ℕ} (hx : 0 ≤ x) : 
x ^ (n) / (n)! ≤ complex.abs (complex.exp x) :=
begin
  simp only [abs_exp_of_real],
  refine pow_div_factorial_le_exp_nonneg hx,
end 


lemma abs_exp_real_eq_abs_exp_complex {x : ℝ} (a : ℂ) : 
complex.abs (complex.exp (a.re * ↑x ^ 2)) = complex.abs (complex.exp (a * ↑x ^ 2)) :=
begin
  have h₂₁: complex.exp (a * ↑x ^ 2) = complex.exp (a.re * ↑x ^ 2)*complex.exp ((a.im * complex.I) * ↑x ^ 2),
    {nth_rewrite 0 ← (complex.eta a),
    rw [complex.mk_eq_add_mul_I, add_mul, complex.exp_add],},
  have h₂₂: complex.abs (complex.exp (a.re * ↑x ^ 2)*complex.exp ((a.im * complex.I) * ↑x ^ 2))=complex.abs (complex.exp (a.re * ↑x ^ 2)) * complex.abs (complex.exp ((a.im * complex.I) * ↑x ^ 2)),
    {rw [← complex.norm_eq_abs,← complex.norm_eq_abs,← complex.norm_eq_abs,norm_mul],},
  rw [h₂₁, h₂₂, mul_comm (↑(a.im) * I) (↑x ^ 2), ← mul_assoc,← of_real_pow],
  nth_rewrite 2 ← of_real_mul,
  rw [complex.abs_exp_of_real_mul_I,mul_one],
end 


lemma pow_sq_div_factorial_le_abs_exp_nonneg {x : ℝ} {n : ℕ} {a : ℂ} (hx : 0 ≤ x) (ha : 0 < a.re) : 
(a.re^n* x ^ (2* (n))) / (n)! ≤ complex.abs (complex.exp (a * ↑x ^ 2)) :=
begin
  have h₁:= pow_div_factorial_le_abs_exp_nonneg ((zero_le_mul_left ha).mpr (sq_nonneg x)),
  rw mul_pow at h₁,
  have h₂:=abs_exp_real_eq_abs_exp_complex a, 
  rw [pow_mul,← h₂,← of_real_pow,← of_real_mul],
  exact h₁,
end 


lemma inv_exp_sq_le_factorial_div_pow_sq_with_a {x : ℝ} {n : ℕ} {a : ℂ} (hx : 0 < x) (ha : 0 < a.re) : 
1/complex.abs (complex.exp (a * x^2)) ≤ (n)! /(a.re^n* x ^ (2* (n))) := 
begin
  cases (lt_iff_le_and_ne.mp hx) with hle hne_zero,
  have h₁:=pow_sq_div_factorial_le_abs_exp_nonneg hle ha,
  have h₂: 0 < complex.abs (complex.exp (a * x^2)), by {rw complex.abs_exp, refine real.exp_pos _,},
  have h₃: 0 < x ^ (2* (n)),by {rw [mul_comm, pow_mul,sq_pos_iff], exact pow_ne_zero (n) (hne_zero.symm),},
  have h₄: 0 < (↑(n)!: ℝ), by {norm_cast, exact nat.factorial_pos (n),},
  have h₅: (a.re ^ n* x ^ (2 * n)) / ↑n! ≤ complex.abs (complex.exp (a * x^2))↔ (a.re ^ n * x ^ (2 * n)) ≤ ↑n! *complex.abs (complex.exp (a * x^2)), 
  by convert div_le_iff' h₄,
  rw [div_le_div_iff h₂ (mul_pos (pow_pos ha n) (h₃)), one_mul],
  exact h₅.1 h₁,
end 


lemma neg_expo_a {x : ℝ} {a : ℂ} : 
1/complex.abs (complex.exp (a * x^2)) = complex.abs (complex.exp (-a * x^2)) :=
begin 
  rw [neg_mul,complex.exp_neg, one_div,map_inv₀],
end 


lemma pow_sq_exp_neg_sq_le_factorial {x : ℝ} {n : ℕ} {a : ℂ} (hx : 0 < x) (ha : 0 < a.re) : 
x ^(2 * (n)) *complex.abs (complex.exp (-a * x^2)) ≤ (n)!/a.re^n :=
begin
  cases (lt_iff_le_and_ne.mp hx) with hle hne_zero,
  have h₁:=inv_exp_sq_le_factorial_div_pow_sq_with_a hx ha,
  rw [neg_expo_a,le_div_iff,mul_comm,mul_assoc,mul_comm,← le_div_iff] at h₁,
  exact h₁,  exact pow_pos ha n,  exact mul_pos (pow_pos ha n) (pow_pos hx (2 * n)),
end 


lemma pow_exp_neg_sq_le_factorial_div_pow {x : ℝ} {n : ℕ} {a : ℂ} (hx : 0 < x) (ha : 0 < a.re) : 
x ^ (n) *complex.abs (complex.exp (-a * x^2)) ≤ (n)! /(a.re^n * x ^ (n)) :=
begin
  have h₁:=pow_sq_exp_neg_sq_le_factorial hx ha,
  rw [mul_comm 2 (n),pow_mul, sq,mul_assoc,← le_div_iff' (pow_pos hx n),div_div] at h₁,
  exact h₁,
end 


lemma cexp_re {a : ℂ} {x : ℝ} : 
complex.exp (↑-a.re * (x : ℂ) ^ 2)= complex.exp (-((a.re)* (x^2)) : ℝ) :=
begin
  congr,
  norm_cast,
  rw neg_mul,
end


lemma exp_a_neg_sq_le_one {a : ℂ} (ha : 0 < a.re) : 
∀ x : ℝ , complex.abs (complex.exp (-a * x^2)) ≤ 1 :=
begin
  intro x,
  rw [← abs_exp_real_eq_abs_exp_complex (-a)],
  rw [neg_re],
  rw [cexp_re],
  rw [←complex.of_real_exp],
  rw [← complex.norm_eq_abs],
  norm_cast,
  simp only [norm_eq_abs],
  simp only [abs_exp],
  simp only [exp_le_one_iff],
  simp only [right.neg_nonpos_iff],
  rw zero_le_mul_left ha,
  positivity,
end


lemma pow_exp_neg_sq_bounded_pos_le_one {x : ℝ} {a : ℂ} {n : ℕ} (ha : 0 < a.re) 
(hx : x > 0) (h : x ≤ 1) : x ^ n * complex.abs (cexp (-a * ↑x ^ 2)) ≤ max 1 (↑n! / a.re ^ n) :=
begin
  rw mul_comm,
  refine le_trans (mul_le_one _ _ _) _,
  refine exp_a_neg_sq_le_one ha x,
  refine pow_nonneg (le_of_lt hx) (n),
  refine pow_le_one (n) (le_of_lt hx) h,
  simp only [le_max_iff, le_refl, true_or],
end


lemma pow_exp_neg_sq_bounded_pos_one_lt {x : ℝ} {a : ℂ} {n : ℕ} (ha : 0 < a.re) 
(hx : x > 0) (h : 1 < x) : x ^ n * complex.abs (cexp (-a * ↑x ^ 2)) ≤ max 1 (↑n! / a.re ^ n) :=
begin
  have h₁:=pow_exp_neg_sq_le_factorial_div_pow hx ha,
  rw ← div_div at h₁,
  refine le_trans (le_trans h₁ (div_le_self _ (one_le_pow_of_one_le  (le_of_lt h) n))) _,
  have h₃:  (0: ℝ) < ↑n!, by {norm_cast, exact nat.factorial_pos n,},
  have h₄:= le_of_lt (mul_pos h₃ (one_div_pos.mpr (pow_pos ha n))),
  have h₅: ↑n!* (1/a.re^n) = ↑n!/a.re^n, by {simp only [one_div], ring_nf,},
  rw h₅ at h₄,
  refine h₄,
  simp only [le_max_iff, le_refl, or_true],
end


lemma pow_exp_neg_sq_bounded_pos  {a : ℂ} (n : ℕ) (ha : 0 < a.re) : 
∃ (C : ℝ), 1 ≤ C ∧   ∀ x : ℝ, (x > 0 →  x ^ (n) * complex.abs (complex.exp (-a * x^2)) ≤ C) :=
begin
  use max 1 (n!/a.re^n : ℝ),
  split,
  simp only [le_max_iff, le_refl, true_or],
  intros x hx,
  cases le_or_lt x 1,
  {refine pow_exp_neg_sq_bounded_pos_le_one ha hx h},
  {refine pow_exp_neg_sq_bounded_pos_one_lt ha hx h},
end 


lemma pow_exp_neg_sq_bounded_nonneg (n : ℕ) {a : ℂ} (ha : 0 < a.re) :  
∃ (C : ℝ),  ∀ x : ℝ, (x ≥ 0 →  x ^ (n) * complex.abs (complex.exp (-a * x^2)) ≤ C) :=
begin
  have h₁:= pow_exp_neg_sq_bounded_pos n ha,
  obtain ⟨C,h₁⟩:=h₁,
  cases h₁ with h₁₁ h₁₂, 
  use (C),
  intros x hx,
  cases le_or_lt x 0,
  {cases le_or_lt n 0,
  {have h₃: n=0, by linarith, rw [h₃,pow_zero,one_mul],
  refine le_trans (exp_a_neg_sq_le_one ha x) _, exact h₁₁,},
  {have h₂: x =0, by linarith, rw [h₂,zero_pow',zero_mul], linarith, linarith,},},
  {specialize h₁₂ x,  specialize h₁₂ h, refine le_trans h₁₂ _, simp only [le_refl],},
end 


lemma abs_pow_exp_neg_sq_bounded {n : ℕ} {a : ℂ} (ha : 0 < a.re) : 
∃ (C : ℝ),  ∀ x : ℝ, (‖↑x ^ (n) * complex.exp (-a * x^2)‖ ≤ C) :=
begin
  have h₁:=pow_exp_neg_sq_bounded_nonneg n ha,
  obtain ⟨C,h₁⟩:=h₁,
  use C,
  intro x,
  specialize h₁ (|x|),
  specialize h₁ (abs_nonneg x),
  convert h₁,
  simp only [neg_mul, complex.norm_eq_abs, absolute_value.map_mul, complex.abs_pow, 
  abs_of_real, mul_eq_mul_left_iff],
  left,
  norm_cast,
  simp only [pow_bit0_abs],
end 


/-  This lemma is from the library. I made a complex version, as you can see below. -/
lemma fderiv_exp {d : ℕ} {f: (E') → ℝ  } {x : E'} (hc : differentiable_at ℝ f x) :  fderiv ℝ (λx, real.exp (f x)) x = real.exp (f x) • (fderiv ℝ f x) :=by exact hc.has_fderiv_at.exp.fderiv


lemma fderiv_cexp {d : ℕ} {f: (E') → ℂ  } (x : E') (hc : differentiable_at ℝ  f x) : 
fderiv ℝ (λx, complex.exp (f x)) x = complex.exp (f x) • (fderiv ℝ  f x) := by exact hc.has_fderiv_at.cexp.fderiv


lemma fderiv_cexp_id (x : ℂ) : 
fderiv ℝ (λx, complex.exp (x)) x = complex.exp (id x) • (fderiv ℝ id x) :=
begin 
  have h : differentiable_at ℝ id x, by apply differentiable_at_id,
  exact h.has_fderiv_at.cexp.fderiv, 
end 


lemma normed_iterated_fderiv_zero_id {x : E'} : 
‖iterated_fderiv ℝ 0 id x‖ = ‖x‖ := by simp only [norm_iterated_fderiv_zero, id.def]


lemma normed_iterated_fderiv_one_eq_norm_fderiv_id {x : E'} : 
‖iterated_fderiv ℝ 1 id x‖ = ‖fderiv ℝ id x‖ := 
by rw [← zero_add 1, ← norm_iterated_fderiv_fderiv,norm_iterated_fderiv_zero]


lemma normed_iterated_fderiv_eq_norm_continuous_linear_map {x : E'} : 
‖iterated_fderiv ℝ 1 id x‖ = ‖continuous_linear_map.id ℝ E'‖ := 
by rw [normed_iterated_fderiv_one_eq_norm_fderiv_id,fderiv_id]


lemma normed_iterated_fderiv_one_id_le_one {x : E'} : 
‖iterated_fderiv ℝ 1 id x‖ ≤  1 := 
begin 
  rw [normed_iterated_fderiv_eq_norm_continuous_linear_map], 
  exact continuous_linear_map.norm_id_le,
end


lemma normed_iterated_fderiv_one_id_eq_one {x : E'} (h :‖x‖≠0) : 
‖iterated_fderiv ℝ 1 id x‖ =  1 :=
begin 
  rw [normed_iterated_fderiv_eq_norm_continuous_linear_map],
  refine continuous_linear_map.norm_id_of_nontrivial_seminorm _,  use x,
end


lemma fderiv_id_eq_continuous_linear_map : fderiv ℝ (@id E') = (λ (x : E'), continuous_linear_map.id ℝ E'):= by {ext, rw fderiv_id,}


lemma normed_iterated_fderiv_two_id_eq_zero (x : E') : 
‖iterated_fderiv ℝ 2 id x‖ = 0 := 
begin 
  rw [← norm_iterated_fderiv_fderiv, ← zero_add 1, ← norm_iterated_fderiv_fderiv, 
  norm_iterated_fderiv_zero,norm_eq_zero,fderiv_id_eq_continuous_linear_map , 
  fderiv_const, pi.zero_apply],
end


lemma iterated_fderiv_two_id_eq_zero: iterated_fderiv ℝ 2 (@id E') = 0:= 
begin
  ext x, rw [pi.zero_apply, continuous_multilinear_map.zero_apply],
  have h₁: iterated_fderiv ℝ 2 id x = 0, by {rw ← norm_eq_zero, exact normed_iterated_fderiv_two_id_eq_zero x,},
  rw [h₁,continuous_multilinear_map.zero_apply], 
end


lemma deriv_id_coe_complex {x : ℝ} : deriv (λ (y : ℝ), (y : ℂ)) x = 1 := 
has_deriv_at.deriv (has_deriv_at.of_real_comp (has_deriv_at_id x))


lemma differentiable_at_complex_id {x : ℝ} : differentiable_at ℝ (λ (y : ℝ), (y : ℂ)) x := 
complex.of_real_clm.differentiable_at.comp _ (differentiable_at_id)


lemma differentiable_at_const_mul_complex_id {x : ℝ} {a : ℂ} : differentiable_at ℝ (λ (y : ℝ), a * (y : ℂ)) x :=
differentiable_at.mul (differentiable_at_const _) (differentiable_at_complex_id)


lemma differentiable_at_cexp_const_mul_complex_id {x : ℝ} {a : ℂ} : differentiable_at ℝ (λ (y : ℝ), cexp(a * (y : ℂ))) x :=
differentiable_at.cexp differentiable_at_const_mul_complex_id


lemma iterated_deriv_cexp_const_mul {i : ℕ} {a : ℂ} :  
iterated_deriv i (λ (y : ℝ), complex.exp (a * (y : ℂ))) = (λ (y : ℝ), (a)^i *complex.exp (a * (y : ℂ))) :=
begin
  induction i with i hi,
  {simp only [iterated_deriv_zero,pow_zero,one_mul],},
  {rw [iterated_deriv_succ, hi],  funext,
  rw [deriv_const_mul _, deriv_cexp _,deriv_const_mul _, deriv_id_coe_complex, 
  mul_one, mul_comm (cexp (a * ↑x)), ← mul_assoc, nat.succ_eq_add_one, pow_add, pow_one],
  {exact differentiable_at_complex_id},
  {exact differentiable_at_const_mul_complex_id},
  {exact differentiable_at_cexp_const_mul_complex_id,},},
end


lemma norm_iterated_deriv_cexp_const_mul (x : ℝ) {a : ℂ} (i : ℕ) : 
‖iterated_fderiv ℝ i (λ y : ℝ, cexp (-a * y)) x‖ = ‖a‖^i* ‖cexp(-a * x)‖:=
begin
  rw [iterated_fderiv_eq_equiv_comp,linear_isometry_equiv.norm_map,iterated_deriv_cexp_const_mul], dsimp,
  simp only [complex.norm_eq_abs, absolute_value.map_mul, complex.abs_pow, absolute_value.map_neg, mul_eq_mul_left_iff],
  left, rw complex.abs_exp,
end


lemma norm_const_pow_le_max  {a : ℂ} {i n : ℕ} (hn : i ≤ n) :  
(‖a‖ ^ i) ≤  (max (‖a‖ ^ n) 1) :=
begin
  cases le_or_lt (‖a‖) 1,
  {have h₁: 1 ≤ max (‖a‖ ^ n) 1, by {simp only [le_max_iff, le_refl, or_true]},
  exact le_trans (pow_le_one i (norm_nonneg a) h) h₁,},
  {have h₁: ‖a‖ ^ n  ≤ max (‖a‖ ^ n) 1, by {simp only [le_max_iff, le_refl, true_or]},
  exact le_trans (pow_le_pow (le_of_lt h) (hn)) h₁,},
end


def inner_const (a : E') : E' →L[ℝ] ℝ := 
{to_fun := λ (b : E'), has_inner.inner a b, 
 map_add':= 
  begin 
    intros x y, 
    rw [← inner_product_space.conj_symm, inner_product_space.add_left, 
    map_add, inner_product_space.conj_symm,inner_product_space.conj_symm ],
  end,
 map_smul':=
  begin
    intros r x,
    rw [← inner_product_space.conj_symm, inner_product_space.smul_left],
    simp only [is_R_or_C.conj_to_real, ring_hom.id_apply], 
    simp only [algebra.id.smul_eq_mul, mul_eq_mul_left_iff],
    left,
    rw ←inner_product_space.conj_symm,
    exact is_R_or_C.conj_to_real,
  end,}


lemma inner_const_eq (a b : E') : inner_const a b = has_inner.inner a b := rfl


lemma has_inner_map_add : ∀ (x y : E'), inner_const (x + y) = inner_const x + inner_const y :=
begin
  intros x y,
  ext,
  simp only [continuous_linear_map.add_apply],
  repeat {rw inner_const_eq},
  exact inner_product_space.add_left x y x_1,
end


lemma has_inner_map_mul : ∀ (r : ℝ) (x : E'), inner_const (r • x) = r • inner_const x:=
begin
  intros r x,
  ext,
  rw inner_const_eq,
  rw inner_product_space.smul_left _ _,
  simp only [is_R_or_C.conj_to_real, ring_hom.id_apply, continuous_linear_map.coe_smul', pi.smul_apply, algebra.id.smul_eq_mul,
  mul_eq_mul_left_iff],
  left,
  rw inner_const_eq ,
end


lemma norm_inner_const_le_bound : ∀ (x : E'), ‖inner_const x‖ ≤ 1 * ‖x‖:=
begin
  intro x,
  simp,
  refine continuous_linear_map.op_norm_le_bound _ (norm_nonneg _) _,
  intro y,
  rw inner_const_eq x y,
  refine norm_inner_le_norm _ _,
end


def B : E' →L[ℝ] E' →L[ℝ] ℝ :=
{to_fun := λ (a : E'), inner_const a,
 map_add':= has_inner_map_add,
 map_smul':= has_inner_map_mul,
 cont:= 
  begin
  dsimp only, show continuous (λ (a : E'), inner_const a),
  refine continuous_of_linear_of_bound 
  has_inner_map_add has_inner_map_mul 
  norm_inner_const_le_bound,
  end}


lemma B_eq_inner {x y : E'} : B x y = has_inner.inner x y := rfl


lemma norm_iterated_fderiv_n.succ.succ {n : ℕ} (x : E') : 
‖iterated_fderiv ℝ (n+1+1) id x‖ = 0 := 
begin 
  induction n with n hn, 
  {rw [zero_add, iterated_fderiv_two_id_eq_zero],simp,},
  have h₁: iterated_fderiv ℝ (n.succ + 2) id = iterated_fderiv ℝ (n.succ +1  + 1) id, by {simp,},
  rw [h₁, ← norm_iterated_fderiv_fderiv, ← norm_iterated_fderiv_fderiv, fderiv_id_eq_continuous_linear_map],
  simp only [fderiv_const,norm_eq_zero],
  rw [nat.succ_eq_add_one, pi.zero_def],
  simp only [iterated_fderiv_zero_fun, pi.zero_apply],
end


lemma norm_iterated_fderiv_n.succ {n : ℕ} {x : E'} : 
‖iterated_fderiv ℝ (n+1) id x‖ ≤ 1  := 
begin 
  induction n with n hn, 
  {rw zero_add,exact normed_iterated_fderiv_one_id_le_one,},
  {rw [nat.succ_eq_add_one, norm_iterated_fderiv_n.succ.succ],
  apply zero_le_one,},
end


lemma nat_mul_iterated_fderiv_id_mul_le_nat {i d : ℕ} {x : E'} : 
↑i * ‖iterated_fderiv ℝ (0 + 1) id x‖ * ‖iterated_fderiv ℝ (d + 1) id x‖ ≤ ↑i  :=
begin
  rw [mul_assoc (i : ℝ)],
  nth_rewrite 1 ←mul_one (i:ℝ),  
  refine mul_le_mul rfl.ge _ _ _,
  rw ← one_mul (1: ℝ),
  refine mul_le_mul _ _ (norm_nonneg _) (zero_le_one),
  refine norm_iterated_fderiv_n.succ,
  refine norm_iterated_fderiv_n.succ,
  positivity,  positivity,
end


lemma nat_le_pow_nat₁ {i n : ℕ} {x : E'} (hi : 1 < i) 
(hn : i ≤ n) (hxn : 1 < ‖ x ‖) : (i : ℝ)  ≤ ((n : ℝ)*2 * ‖x‖)^i :=
begin
  have h₁: (n : ℝ) ≤ (n : ℝ)^i, by {norm_cast,refine nat.le_self_pow _ _,linarith,},
  have h₂: (i : ℝ) ≤ (n : ℝ), by {norm_cast, exact hn,},
  have h₃: (2 * ‖x‖) ^ i = (2 * ‖x‖) ^ (i : ℝ), by {norm_cast,},
  rw [← mul_one (i:ℝ), mul_assoc (n : ℝ) _ _, mul_pow],
  refine mul_le_mul _ _ zero_le_one _,
  exact le_trans h₂ h₁,
  rw h₃,
  refine real.one_le_rpow _ _,
  linarith,
  positivity,
  positivity,
end


lemma sum_bound_one_lt {i n : ℕ} {x : E'} (hi : 1 < i) (hn : i ≤ n) (hxn : 1 < ‖ x ‖) : 
∑ (j : ℕ) in range (i + 1), ↑(i.choose j) * ‖iterated_fderiv ℝ j id x‖ * ‖iterated_fderiv ℝ (i - j) id x‖ ≤  ((n : ℝ) *2 * ‖x‖) ^ i :=
begin
  have h₁:  2 ≤ i, by linarith,
  have h₂:= nat.exists_eq_add_of_le' h₁,
  obtain ⟨d,h₂⟩:=h₂,
  rw [h₂, finset.sum_range_succ', finset.sum_range_succ'],
  simp_rw norm_iterated_fderiv_n.succ.succ,
  simp only [mul_zero, zero_mul, sum_const_zero, zero_add, 
  nat.choose_one_right, nat.cast_add, algebra_map.coe_one,
  nat.choose_zero_right, norm_iterated_fderiv_zero, id.def, one_mul],
  have h₄: ‖iterated_fderiv ℝ (d + 2 - 0) id x‖ = ‖iterated_fderiv ℝ (d + 2) id x‖, by congr,
  have h₅: ‖iterated_fderiv ℝ (d + 2 - (0 + 1)) id x‖ = ‖iterated_fderiv ℝ (d + 1) id x‖, by congr,
  have h₆: ((i : ℕ) : ℝ) = ((d : ℝ)  + ((2: ℕ) : ℝ)), by  {simp_rw h₂,norm_cast,},
  rw [h₄, h₅, norm_iterated_fderiv_n.succ.succ, mul_zero, add_zero, ← h₆, ← h₂],
  refine le_trans nat_mul_iterated_fderiv_id_mul_le_nat (nat_le_pow_nat₁ hi hn hxn),
end 



lemma norm_fderiv_one_mul_x_add_le₁ {n i : ℕ} {x : E'} (hone: 1 = i) (hn : i ≤ n) :
‖iterated_fderiv ℝ 1 id x‖ * ‖x‖ + ‖x‖ * ‖iterated_fderiv ℝ 1 id x‖ ≤ ↑n * 2 * ‖x‖ :=
begin
  have h₁: ‖iterated_fderiv ℝ 1 id x‖ * ‖x‖ + ‖x‖ * ‖iterated_fderiv ℝ 1 id x‖ = ‖iterated_fderiv ℝ 1 id x‖ * 2* ‖x‖ , by ring_nf,
  rw h₁,
  refine mul_le_mul _ rfl.ge (norm_nonneg _) _,
  {refine mul_le_mul _ rfl.ge zero_le_two _,
  refine le_trans normed_iterated_fderiv_one_id_le_one _,
  norm_cast, linarith, positivity,},
  {positivity,},
end


lemma inner_const_bound {x : E'}: ‖inner_const x‖ ≤ 1 * ‖x‖ :=
begin
  refine continuous_linear_map.op_norm_le_bound _ _ _,
  positivity,
  intro y,
  simp,
  rw inner_const_eq,
  refine abs_real_inner_le_norm _ _,
end


lemma sum_norm_iterated_fderiv_le {n i : ℕ} {x : E'} (hi : 1 ≤ i) (hn : i ≤ n) (hx : 1 < ‖ x ‖):
∑ (j : ℕ) in range (i + 1), ↑(i.choose j) * ‖iterated_fderiv ℝ j id x‖ * ‖iterated_fderiv ℝ (i - j) id x‖ ≤ (↑n * 2 * ‖x‖) ^ i :=
begin
  have h1: 1=i ∨  1 <i, by exact eq_or_lt_of_le hi,
  cases h1 with hone hbigger,
  rw [← hone,finset.sum_range_succ'],
  simp only [range_one, sum_singleton, nat.choose_one_right, algebra_map.coe_one, one_mul, norm_iterated_fderiv_zero, id.def,
  nat.choose_succ_self_right],
  have h₁: ‖iterated_fderiv ℝ (0 + 1) id x‖ = ‖iterated_fderiv ℝ (1) id x‖, by simp only,
  have h₂: ‖iterated_fderiv ℝ (1-0) id x‖ =‖iterated_fderiv ℝ (1) id x‖, by simp only,
  rw [h₁,h₂,pow_one],
  refine norm_fderiv_one_mul_x_add_le₁ hone hn,
  refine sum_bound_one_lt hbigger hn hx,
end


lemma inner_bound_one_lt {n : ℕ} {x : E'} (hx : 1 < ‖ x ‖) : 
∀ (i : ℕ), 1 ≤ i → i ≤ n → ‖iterated_fderiv ℝ i (λ (x : E'), ‖x‖ ^ 2) x‖ ≤ ((n : ℝ) *2 * ‖x‖) ^ i  :=
begin
  intros i hi hn,
  have htop: ↑i ≤ (⊤ : ℕ∞), by {refine le_of_lt _, exact with_top.coe_lt_top i,},
  have := continuous_linear_map.norm_iterated_fderiv_le_of_bilinear B cont_diff_id cont_diff_id x htop,
  simp_rw B_eq_inner at this,
  simp only [id.def] at this, 
  simp_rw real_inner_self_eq_norm_sq at this , 
  refine le_trans this _,
  rw [← one_mul ((↑n * 2 * ‖x‖) ^ i), mul_comm (‖B‖) _, mul_comm (1) ((↑n * 2 * ‖x‖) ^ i)],
  refine mul_le_mul _ _ (norm_nonneg _) _,
  {refine sum_norm_iterated_fderiv_le hi hn hx},
  {unfold B,  refine continuous_linear_map.op_norm_le_bound _ zero_le_one _,
  intro x,  dsimp,  refine inner_const_bound,},
  {positivity,},
end


lemma nat_le_pow_nat₂  {n i : ℕ} (hi : 1 < i) (hn : i ≤ n) : 
(i : ℝ)  ≤ ((n : ℝ)*2)^i := 
begin 
  rw [← mul_one (i:ℝ),mul_pow],
  refine mul_le_mul _ _ zero_le_one _,
  have h₁: (n : ℝ) ≤ (n : ℝ)^i, by {norm_cast,refine nat.le_self_pow _ _,linarith,},
  have h₂: (i : ℝ) ≤ (n : ℝ), by {norm_cast, exact hn,},
  exact le_trans h₂ h₁,
  norm_cast,
  refine nat.one_le_pow i 2 zero_lt_two,
  positivity,
end


lemma sum_bound_le_one {i n : ℕ} {x : E'} (hi : 1 < i) (hn : i ≤ n) (hxn : ‖ x ‖ ≤ 1) : 
∑ (j : ℕ) in range (i + 1), ↑(i.choose j) * ‖iterated_fderiv ℝ j id x‖ * ‖iterated_fderiv ℝ (i - j) id x‖ ≤  ((n : ℝ) *2) ^ i :=
begin
  have h₁:  2 ≤ i, by linarith,
  have h₂:= nat.exists_eq_add_of_le' h₁,
  obtain ⟨d,h₂⟩:=h₂,
  rw [h₂, finset.sum_range_succ', finset.sum_range_succ'],
  simp_rw norm_iterated_fderiv_n.succ.succ,
  simp only [mul_zero, zero_mul, sum_const_zero, zero_add, nat.choose_one_right, nat.cast_add, algebra_map.coe_one,
  nat.choose_zero_right, norm_iterated_fderiv_zero, id.def, one_mul],
  have h₄: ‖iterated_fderiv ℝ (d + 2 - 0) id x‖ = ‖iterated_fderiv ℝ (d + 2) id x‖, by congr,
  have h₅: ‖iterated_fderiv ℝ (d + 2 - (0 + 1)) id x‖ = ‖iterated_fderiv ℝ (d + 1) id x‖, by congr,
  have h₇: ((i : ℕ) : ℝ) = ((d : ℝ)  + ((2: ℕ) : ℝ)), by  {simp_rw h₂,norm_cast,},
  rw [h₄,h₅, norm_iterated_fderiv_n.succ.succ, mul_zero,add_zero,← h₇,←h₂],
  refine le_trans (nat_mul_iterated_fderiv_id_mul_le_nat) (nat_le_pow_nat₂ hi hn),
end 


lemma norm_fderiv_one_mul_x_add_le₂ (x : E') {n i : ℕ} (hxn :  ‖ x ‖ ≤ 1) (hi : 1 ≤  i) (hn : i ≤ n) : 
‖iterated_fderiv ℝ 1 id x‖ * ‖x‖ + ‖x‖ * ‖iterated_fderiv ℝ 1 id x‖ ≤ 2 * ↑n :=
begin 
  have h : ‖iterated_fderiv ℝ 1 id x‖ * ‖x‖ + ‖x‖ * ‖iterated_fderiv ℝ 1 id x‖ = 2* (‖x‖ * ‖iterated_fderiv ℝ 1 id x‖), by ring_nf,
  rw h,
  refine mul_le_mul rfl.ge _ _ (zero_le_two),
  rw ← one_mul (n : ℝ),
  refine mul_le_mul hxn _ (norm_nonneg _) zero_le_one,
  refine le_trans normed_iterated_fderiv_one_id_le_one _,
  norm_cast,
  refine le_trans hi hn,
  positivity,
end 


lemma sum_norm_iterated_fderiv_le₂ {n i : ℕ} {x : E'} (hi : 1 ≤ i) (hn : i ≤ n) (hx : ‖ x ‖ ≤ 1):
∑ (j : ℕ) in range (i + 1), ↑(i.choose j) * ‖iterated_fderiv ℝ j id x‖ * ‖iterated_fderiv ℝ (i - j) id x‖ ≤ (2 * ↑n) ^ i:=
begin
  have h1: 1=i ∨  1 <i, by exact eq_or_lt_of_le hi,
  cases h1 with hone hbigger,
  rw [← hone,finset.sum_range_succ'],
  simp only [range_one, sum_singleton, nat.choose_one_right, algebra_map.coe_one, one_mul, norm_iterated_fderiv_zero, id.def,
  nat.choose_succ_self_right],
  have h₁: ‖iterated_fderiv ℝ (0 + 1) id x‖ = ‖iterated_fderiv ℝ (1) id x‖, by simp only,
  have h₂: ‖iterated_fderiv ℝ (1-0) id x‖ =‖iterated_fderiv ℝ (1) id x‖, by simp only,
  rw [h₁,h₂,pow_one],
  refine norm_fderiv_one_mul_x_add_le₂ x hx hi hn, 
  rw mul_comm (2) (n : ℝ), 
  refine (sum_bound_le_one hbigger hn hx),
end


lemma inner_bound_le_one {n : ℕ} {x : E'} (hx :  ‖ x ‖ ≤ 1) : 
∀ (i : ℕ), 1 ≤ i → i ≤ n → ‖iterated_fderiv ℝ i (λ (x : E'), ‖x‖ ^ 2) x‖ ≤  (2 * (n : ℝ))^i  :=
begin
  intros i hi hn,
  have hf: cont_diff ℝ ⊤ (@id E') :=  cont_diff_id,
  have htop: ↑i ≤ (⊤ : ℕ∞), by {refine le_of_lt _, exact with_top.coe_lt_top i,},
  have := continuous_linear_map.norm_iterated_fderiv_le_of_bilinear B hf hf x htop,
  simp_rw B_eq_inner at this, simp only [id.def] at this, 
  simp_rw real_inner_self_eq_norm_sq at this , 
  refine le_trans this _,
  rw [← one_mul ((2 * (n : ℝ)) ^ i), mul_comm (‖B‖) _, mul_comm (1) ((2* (n : ℝ)) ^ i)],
  refine mul_le_mul _ _ (norm_nonneg _) _,
  {refine sum_norm_iterated_fderiv_le₂ hi hn hx}, 
  {unfold B,
  refine continuous_linear_map.op_norm_le_bound _ zero_le_one _,
  intro x,
  refine inner_const_bound,},
  {positivity,},
end


lemma cont_diff_cexp_const_mul (N : ℕ∞) (a : ℂ) : 
cont_diff ℝ N (λ (y : ℝ), cexp (-a * y)) := 
begin 
  refine cont_diff.cexp (cont_diff.mul cont_diff_const _),
  refine cont_diff.comp complex.of_real_clm.cont_diff cont_diff_id,
end


lemma norm_pow_max_eq {m n : ℕ} {a : ℂ} (ha : 0 < a.re) : 
‖x‖ ^ (2 * max n m) = (a.re ^ max n m)⁻¹ * (a.re ^ max n m * ‖x‖ ^ (2 * max n m)) :=
begin
  repeat {rw ← mul_assoc,},
  rw [mul_comm, mul_comm ((a.re ^ max n m)⁻¹), ← div_eq_mul_inv, div_self _, one_mul],
  exact pow_ne_zero _  (ne_of_gt ha),
end


lemma pow_sq_exp_neg_sq_le_factorial'  (x : ℝ) (n : ℕ) {a : ℂ} (hx : 0 < x) (ha : 0 < a.re) : 
x ^(2 * (n)) *complex.abs (complex.exp (-a * x^2)) ≤ (n)!/a.re^n := pow_sq_exp_neg_sq_le_factorial hx ha


lemma const_pow_mul_norm_exp_bound {x : E'} {a : ℂ} {i n : ℕ} 
(hn : i ≤ n) (hx : 0 < ‖x‖) (ha : 0 < a.re) : 
‖a‖^i* ‖cexp(-a * (‖x‖: ℂ)^2)‖ ≤ max (‖a‖ ^ n) 1 * (↑n! / (a.re ^ n * ‖x‖ ^ (2 * n))) :=
begin
  have h₁:= pow_sq_exp_neg_sq_le_factorial' (‖x‖) n hx ha, rw [← le_div_iff' _,div_div] at h₁,
  have h₂: ‖a‖ ^ i * ‖cexp (-a * ↑‖x‖ ^ 2)‖ ≤ (max (‖a‖ ^ n) 1) * ‖cexp (-a * ↑‖x‖ ^ 2)‖,
  by {refine mul_le_mul (norm_const_pow_le_max hn) rfl.ge (norm_nonneg _) _, positivity,},
  refine le_trans h₂ _,
  {refine mul_le_mul rfl.ge h₁ _ _, positivity, positivity,},
  {positivity,},
end


theorem bound_iterated_deriv_norm_ge_one (n : ℕ) (m : ℕ) (a : ℂ) 
(ha : 0 < a.re) (x : E') (hxn : 1 < ‖ x ‖) :
‖x‖^m * ‖iterated_fderiv ℝ n ((λ (y : E'), cexp (- a * ‖y‖^2))) x‖ ≤ n! * ((max (complex.abs a ^ max n m) 1)/a.re^(max n m))* (max n m)! * (n : ℝ) ^ n* 2^n := 
begin 
  have hpos': 0 < ‖x‖, by positivity,
  have hpos: 0 < ‖x‖ ^ m, by positivity,
  set g := (λ (y : ℝ), cexp (- a * y)) with hg, 
  set f := (λ (y : E'), ‖y‖^2)  with hf, 
  have hcomp : g ∘ f = (λ (y : E'), cexp (-a * ‖y‖^2)), by {rw [hg, hf, function.comp], simp only [of_real_pow],},
  have hleq := norm_iterated_fderiv_comp_le' g f n ⊤ (cont_diff_cexp_const_mul ⊤ a) (cont_diff_norm_sq ℝ) _ x ((max (‖a‖ ^ max n m) 1) * (↑(max n m)! / (a.re ^ max n m* ‖x‖^(2* (max n m))))) ((n : ℝ)*2* ‖x‖) _ _,
  rw [hcomp, ← mul_le_mul_left hpos] at hleq, 
  refine le_trans hleq _, field_simp, rw [div_le_iff, mul_pow],
  have h₁ : ‖x‖ ^ m * (↑n! * (max (complex.abs a ^ max n m) 1 * ↑(max n m)!) * (((n : ℝ) *2) ^ n * ‖x‖ ^ n)) = (n!  *↑(max n m)! * (n : ℝ)^n*2^n)* ((max (complex.abs a ^ max n m) 1) * ‖x‖ ^ (m + n)), by ring_exp, 
  have h₂: ↑n! * max (complex.abs a ^ max n m) 1 * ↑(max n m)! * (n : ℝ) ^ n *2 ^ n / a.re ^ max n m * (a.re ^ max n m * ‖x‖ ^ (2 * max n m)) = ↑n! * ↑(max n m)! * (n : ℝ) ^ n * 2 ^ n  * (((max (complex.abs a ^ max n m) 1) / a.re ^ max n m) * (a.re ^ max n m * ‖x‖ ^ (2 * max n m))), by ring_exp,
  rw [h₁, h₂],
  apply mul_le_mul_of_nonneg_left , 
  rw [div_eq_mul_inv, mul_assoc, ← norm_pow_max_eq ha],
  apply mul_le_mul_of_nonneg_left , 
  rw [pow_le_pow_iff, two_mul] , 
  refine add_le_add (le_max_right n m) (le_max_left n m),
  {exact hxn,},
  {positivity,}, 
  {positivity,}, 
  {positivity,}, 
  {exact le_top,},
  {intros i hi, rw norm_iterated_deriv_cexp_const_mul (f x) i, rw hf, dsimp, 
  have h₁:= le_trans hi (le_max_left n m),
  have h₂:= const_pow_mul_norm_exp_bound h₁ hpos' ha,
  simp only [complex.norm_eq_abs] at h₂,
  simp only [of_real_pow],
  refine h₂,},
  {refine inner_bound_one_lt hxn,} ,  
end


lemma complex.abs_pow_nat_le_max {a : ℂ} {n m i : ℕ} (hn : i≤ n) : 
(complex.abs a) ^ i * 1 ≤ max ((complex.abs a) ^ max n m) 1:=
begin
  rw mul_one, 
  cases le_or_lt (complex.abs a) 1,
  {rw le_max_iff, right, refine pow_le_one _ _ h, positivity,},
  {rw le_max_iff, left, refine pow_le_pow (le_of_lt h) _ , rw le_max_iff, left, exact hn,},
end


lemma gaussian_le_one {a:ℂ} (ha: 0<a.re): ∀ x:E', ‖(λ (x : E'), cexp (-a * ↑‖x‖ ^ 2)) x‖ ≤ 1:=
begin
  intro x,
  simp only [neg_mul, complex.norm_eq_abs, log_one, exp_zero],
  rw complex.abs_exp,
  simp only [neg_re, mul_re, neg_sub, exp_le_one_iff, sub_nonpos],
  norm_cast,
  simp only [mul_zero],
  have h₀: 0 ≤  ‖x‖^2, by simp only [pow_nonneg, norm_nonneg],
  exact (zero_le_mul_left ha).mpr h₀,
end


theorem bound_iterated_deriv_norm_le_one {x : E'} {n m : ℕ} {a : ℂ} 
(ha : 0 < a.re) (hxn :  ‖ x ‖ ≤ 1) :
 ‖x‖^m * ‖iterated_fderiv ℝ n ((λ (y : E'), cexp (- a * ‖y‖^2))) x‖ ≤ n! * ((max (complex.abs a ^ max n m) 1)) * ((n : ℝ) * 2)^n := 
begin 
  set g := (λ (y : ℝ), cexp (- a * y)) with hg, 
  set f := (λ (y : E'), ‖y‖^2)  with hf, 
  have hcomp : g ∘ f = (λ (y : E'), cexp (-a * ‖y‖^2)), by {rw [hg, hf, function.comp], simp only [of_real_pow],},
  have hleq := norm_iterated_fderiv_comp_le' g f n ⊤ (cont_diff_cexp_const_mul ⊤ a) (cont_diff_norm_sq ℝ) _ x ((max (complex.abs a ^ max n m) 1)) ((n : ℝ)*2) _ _,
  rw ← one_mul (↑n! * max (complex.abs a ^ max n m) 1 * (↑n * 2) ^ n),
  refine mul_le_mul (pow_le_one _ (norm_nonneg _) hxn) _ (norm_nonneg _) (zero_le_one),
  rw [hcomp] at hleq, 
  refine hleq,
  {exact le_top,},
  {intros i hi, rw norm_iterated_deriv_cexp_const_mul (f x) i, rw hf, dsimp, 
  simp only [of_real_pow],
  refine le_trans _ (complex.abs_pow_nat_le_max hi),
  {refine mul_le_mul rfl.ge (gaussian_le_one ha x) _ _, positivity, positivity,},},
  {rw mul_comm (n : ℝ) 2,
  refine inner_bound_le_one hxn,} , 
end


theorem bound_iterated_deriv_norm {n m : ℕ} {x : E'} {a : ℂ} (ha : 0 < a.re)  :
 ‖x‖^m * ‖iterated_fderiv ℝ n ((λ (y : E'), cexp (- a * ‖y‖^2))) x‖ ≤ max (n! * ((max (complex.abs a ^ max n m) 1)/a.re^(max n m))* (max n m)! * (n : ℝ) ^ n* 2^n) (n! * ((max (complex.abs a ^ max n m) 1)) * ((n : ℝ) * 2)^n) := 
begin 
  cases le_or_lt (‖x‖) 1,
  {rw le_max_iff,  right,  exact bound_iterated_deriv_norm_le_one ha h,},
  {rw le_max_iff,  left,  exact bound_iterated_deriv_norm_ge_one n m a ha x h,},
end


theorem gaussian_decay  {a : ℂ} (ha : 0 < a.re) :
 ∀ (k n : ℕ), ∃ (C : ℝ), ∀ (x : E'),‖x‖^k * ‖iterated_fderiv ℝ n ((λ (y : E'), cexp (- a * ‖y‖^2))) x‖ ≤ C := 
begin 
  intros k n,
  use (max (n! * ((max (complex.abs a ^ max n k) 1)/a.re^(max n k))* (max n k)! * (n : ℝ) ^ n* 2^n) (n! * ((max (complex.abs a ^ max n k) 1)) * ((n : ℝ) * 2)^n)),
  intro x,
  refine bound_iterated_deriv_norm ha,
end


def gaussian {a : ℂ} (ha :0<a.re) : schwartz_map E' ℂ :=
{ to_fun := λ x : E', complex.exp (-a * ‖x‖^2),
smooth' :=
begin
  refine cont_diff.comp _ _,
  {apply cont_diff.cexp (cont_diff_id),},
  refine cont_diff.mul cont_diff_const _,
  norm_cast,
  refine cont_diff.comp _ _,
  exact of_real_clm.cont_diff,
  exact cont_diff_norm_sq ℝ ,
end,
decay' :=gaussian_decay ha,}


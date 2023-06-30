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
import analysis.calculus.cont_diff
import analysis.calculus.iterated_deriv
import analysis.special_functions.exp_deriv
import number_theory.dioph
import analysis.complex.real_deriv
import analysis.special_functions.gaussian
import analysis.fourier.fourier_transform

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

lemma pow_div_factorial_le_exp_sum_pow_div_factorial {x : ℝ} {n : ℕ} (hx : 0 ≤ x): 
x^n / n! ≤ (∑ (j : ℕ) in range n.succ, (x ^ j / j!: ℂ)).re:=
begin
  have h: ((↑x : ℂ) ^n/ ↑n!).re = x ^ n / n!,  by  rw [← of_real_pow, ← of_real_nat_cast, ← of_real_div, of_real_re],
  rw [sum_range_succ, add_re, h,← coe_re_add_group_hom, (re_add_group_hom).map_sum, coe_re_add_group_hom ],
  refine le_add_of_nonneg_of_le (sum_nonneg (λ m hm, _)) le_rfl,
  rw [← of_real_pow, ← of_real_nat_cast, ← of_real_div, of_real_re],
  exact div_nonneg (pow_nonneg hx _) (nat.cast_nonneg _),
end


lemma zero_le_sum_pow_div_factorial {x : ℝ} {n s: ℕ} (hx : 0 ≤ x): 
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


lemma pow_div_factorial_le_abs_exp_nonneg {x : ℝ} {n : ℕ} (hx : 0 ≤ x): 
x ^ (n) / (n)! ≤ complex.abs (complex.exp x) :=
begin
  simp only [abs_exp_of_real],
  refine pow_div_factorial_le_exp_nonneg hx,
end 


lemma abs_exp_real_eq_abs_exp_complex {x : ℝ} (a : ℂ): 
complex.abs (complex.exp (a.re * ↑x ^ 2)) = complex.abs (complex.exp (a * ↑x ^ 2)):=
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
(a.re^n*x ^ (2*(n))) / (n)! ≤ complex.abs (complex.exp (a * ↑x ^ 2)) :=
begin
  have h₁:= pow_div_factorial_le_abs_exp_nonneg ((zero_le_mul_left ha).mpr (sq_nonneg x)),
  rw mul_pow at h₁,
  have h₂:=abs_exp_real_eq_abs_exp_complex a, 
  rw [pow_mul,← h₂,← of_real_pow,← of_real_mul],
  exact h₁,
end 


lemma inv_exp_sq_le_factorial_div_pow_sq_with_a {x : ℝ} {n : ℕ} {a : ℂ} (hx : 0 < x) (ha : 0 < a.re) : 
1/complex.abs (complex.exp (a*x^2)) ≤ (n)! /(a.re^n*x ^ (2*(n))):= 
begin
  cases (lt_iff_le_and_ne.mp hx) with hle hne_zero,
  have h₁:=pow_sq_div_factorial_le_abs_exp_nonneg hle ha,
  have h₂: 0 < complex.abs (complex.exp (a*x^2)), by {rw complex.abs_exp, refine real.exp_pos _,},
  have h₃: 0 < x ^ (2*(n)),by {rw [mul_comm, pow_mul,sq_pos_iff], exact pow_ne_zero (n) (hne_zero.symm),},
  have h₄: 0 < (↑(n)!: ℝ), by {norm_cast, exact nat.factorial_pos (n),},
  have h₅: (a.re ^ n*x ^ (2 * n)) / ↑n! ≤ complex.abs (complex.exp (a*x^2))↔ (a.re ^ n *x ^ (2 * n)) ≤ ↑n! *complex.abs (complex.exp (a*x^2)), 
  by convert div_le_iff' h₄,
  rw [div_le_div_iff h₂ (mul_pos (pow_pos ha n) (h₃)), one_mul],
  exact h₅.1 h₁,
end 


lemma neg_expo_a {x : ℝ} {a : ℂ}: 
1/complex.abs (complex.exp (a*x^2)) = complex.abs (complex.exp (-a*x^2)):=
begin 
  rw [neg_mul,complex.exp_neg, one_div,map_inv₀],
end 


lemma pow_sq_exp_neg_sq_le_factorial {x : ℝ} {n : ℕ} {a : ℂ} (hx : 0 < x) (ha : 0 < a.re) : 
x ^(2 * (n)) *complex.abs (complex.exp (-a*x^2)) ≤ (n)!/a.re^n :=
begin
  cases (lt_iff_le_and_ne.mp hx) with hle hne_zero,
  have h₁:=inv_exp_sq_le_factorial_div_pow_sq_with_a hx ha,
  rw [neg_expo_a,le_div_iff,mul_comm,mul_assoc,mul_comm,← le_div_iff] at h₁,
  exact h₁,  exact pow_pos ha n,  exact mul_pos (pow_pos ha n) (pow_pos hx (2 * n)),
end 


lemma pow_exp_neg_sq_le_factorial_div_pow {x : ℝ} {n : ℕ} {a : ℂ} (hx : 0 < x) (ha : 0 < a.re) : 
x ^ (n) *complex.abs (complex.exp (-a*x^2)) ≤ (n)! /(a.re^n * x ^ (n)) :=
begin
  have h₁:=pow_sq_exp_neg_sq_le_factorial hx ha,
  rw [mul_comm 2 (n),pow_mul, sq,mul_assoc,← le_div_iff' (pow_pos hx n),div_div] at h₁,
  exact h₁,
end 


lemma cexp_re {a : ℂ} {x : ℝ}: 
complex.exp (↑-a.re * (x : ℂ) ^ 2)= complex.exp (-((a.re)* (x^2)) : ℝ):=
begin
  congr,
  norm_cast,
  rw neg_mul,
end


lemma exp_a_neg_sq_le_one {a : ℂ} (ha : 0 < a.re): 
∀ x : ℝ , complex.abs (complex.exp (-a*x^2)) ≤ 1 :=
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
  nlinarith,
end


lemma pow_exp_neg_sq_bounded_pos_le_one {x : ℝ} {a : ℂ} {n : ℕ} (ha : 0 < a.re) 
(hx : x > 0) (h : x ≤ 1): x ^ n * complex.abs (cexp (-a * ↑x ^ 2)) ≤ max 1 (↑n! / a.re ^ n):=
begin
  rw mul_comm,
  refine le_trans (mul_le_one _ _ _) _,
  refine exp_a_neg_sq_le_one ha x,
  refine pow_nonneg (le_of_lt hx) (n),
  refine pow_le_one (n) (le_of_lt hx) h,
  simp only [le_max_iff, le_refl, true_or],
end


lemma pow_exp_neg_sq_bounded_pos_one_lt {x : ℝ} {a : ℂ} {n : ℕ} (ha : 0 < a.re) 
(hx : x > 0) (h : 1 < x): x ^ n * complex.abs (cexp (-a * ↑x ^ 2)) ≤ max 1 (↑n! / a.re ^ n):=
begin
  have h₁:=pow_exp_neg_sq_le_factorial_div_pow hx ha,
  rw ← div_div at h₁,
  refine le_trans (le_trans h₁ (div_le_self _ (one_le_pow_of_one_le  (le_of_lt h) n))) _,
  have h₃:  (0: ℝ) < ↑n!, by {norm_cast, exact nat.factorial_pos n,},
  have h₄:= le_of_lt (mul_pos h₃ (one_div_pos.mpr (pow_pos ha n))),
  have h₅: ↑n!*(1/a.re^n) = ↑n!/a.re^n, by {simp only [one_div], ring_nf,},
  rw h₅ at h₄,
  refine h₄,
  simp only [le_max_iff, le_refl, or_true],
end


lemma pow_exp_neg_sq_bounded_pos  {a : ℂ} (n : ℕ) (ha : 0 < a.re): 
∃ (C : ℝ), 1 ≤ C ∧   ∀ x : ℝ, (x > 0 →  x ^ (n) * complex.abs (complex.exp (-a*x^2)) ≤ C) :=
begin
  use max 1 (n!/a.re^n : ℝ),
  split,
  simp only [le_max_iff, le_refl, true_or],
  intros x hx,
  cases le_or_lt x 1,
  {refine pow_exp_neg_sq_bounded_pos_le_one ha hx h},
  {refine pow_exp_neg_sq_bounded_pos_one_lt ha hx h},
end 


lemma pow_exp_neg_sq_bounded_nonneg (n : ℕ) {a : ℂ} (ha : 0 < a.re):  
∃ (C : ℝ),  ∀ x : ℝ, (x ≥ 0 →  x ^ (n) * complex.abs (complex.exp (-a*x^2)) ≤ C) :=
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
  {have h₂: x=0, by linarith, rw [h₂,zero_pow',zero_mul], linarith, linarith,},},
  {specialize h₁₂ x,  specialize h₁₂ h, refine le_trans h₁₂ _, simp only [le_refl],},
end 


lemma abs_pow_exp_neg_sq_bounded {n : ℕ} {a : ℂ} (ha : 0 < a.re) : 
∃ (C : ℝ),  ∀ x : ℝ, (‖↑x ^ (n) * complex.exp (-a*x^2)‖ ≤ C) :=
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


lemma gaussian_smooth (a : ℂ):  cont_diff ℝ ⊤ (λ (x : ℝ), complex.exp (-a * (x : ℂ) ^ 2)) :=
begin
  refine cont_diff.comp _ _,
  have h₁:= of_real_zero ,
  {apply cont_diff.cexp (cont_diff_id),},
  {refine cont_diff.mul (cont_diff_const) _,
  refine cont_diff.pow _ 2,
  refine cont_diff.comp (of_real_clm.cont_diff) (cont_diff_id),},
end


lemma differentialbe_at_complex_exp {x : ℝ} {a : ℂ} : 
differentiable_at ℝ (λ (y : ℝ), complex.exp (-(a * ↑y ^ 2))) x :=
begin
  simp_rw ←neg_mul,
  refine cont_diff_at.differentiable_at _ le_top ,
  convert cont_diff.cont_diff_at (gaussian_smooth a),
end


lemma deriv_coe_sq {x : ℝ} : 
deriv (λ (y : ℝ), (y : ℂ) ^ 2) x = (2 : ℂ) * (x : ℂ) :=
begin
  norm_cast,
  apply has_deriv_at.deriv _,
  refine has_deriv_at.of_real_comp _,
  convert differentiable_at.has_deriv_at _,
  simp only [deriv_pow'', differentiable_at_id', nat.cast_bit0, algebra_map.coe_one, pow_one, deriv_id'', mul_one],
  apply differentiable_at.pow differentiable_at_id', 
end


lemma deriv_exp_neg_complex_mul_sq (x : ℝ) (a : ℂ):  
deriv (λ (x : ℝ ), complex.exp (-a*x^2)) x = (λ (x : ℝ ), (-2*a*x) * complex.exp (-a*x^2)) x :=
begin
  rw [deriv.comp, complex.deriv_exp,deriv_mul,deriv_const],
  simp only [neg_mul, zero_mul, zero_add, mul_neg, neg_inj],
  rw deriv_coe_sq,
  ring_nf,
  apply differentiable_at_const,
  {norm_cast, apply complex.differentiable_at_coe, apply differentiable_at_pow 2,},
  {refine differentiable_at.comp _ _ _,
  refine differentiable_at.cexp differentiable_at_id',
  refine differentiable_at_id',},
  {norm_cast, 
  refine differentiable_at.mul (differentiable_at_const _) _, 
  refine complex.differentiable_at_coe (differentiable_at_pow 2),},
end


lemma differentiable_at_complex_polynomial {x : ℝ} {p : polynomial ℂ} : 
differentiable_at ℝ (λ (y : ℝ), eval ↑y p) x :=
begin
  show differentiable_at ℝ ( (λ (y : ℂ), eval (y : ℂ) p) ∘ (λ (y : ℝ), complex.of_real_clm y)) x,
  have h₁: differentiable_at ℂ (λ (y : ℂ), eval (y : ℂ) p) x := polynomial.differentiable_at p,
  have h₂: differentiable_at ℝ complex.of_real_clm x := of_real_clm.differentiable_at,  
  exact differentiable_at.comp (x : ℝ) (differentiable_at.restrict_scalars ℝ h₁) h₂,
end


lemma deriv_complex_polynomial {x : ℝ} {p : polynomial ℂ} : 
deriv (λ (y : ℝ), eval (y :ℂ) p) x = eval ↑x (p.derivative):=
begin
  {set e := λ(y : ℂ), eval y p with he,
  have : deriv (λ (y : ℝ), e ↑y) x = eval ↑x (p.derivative),
    {refine has_deriv_at.deriv _,
    refine has_deriv_at.comp_of_real _,
    rw he,
    refine polynomial.has_deriv_at _ _,},
  exact this,},
end


lemma deriv_iterative_exp_neg_sq (n : ℕ) (a : ℂ): 
∃ p : (polynomial ℂ), ∀ x : ℝ , 
deriv^[n] (λ (x : ℝ ), complex.exp (-a*x^2)) x = (λ (x : ℝ ), (p.eval x) * complex.exp (-a*x^2)) x :=
begin
  induction n with n hn, 
  {use (1: (polynomial ℂ)), intro x, simp only [function.iterate_zero, id.def, neg_mul,eval_one,one_mul],},
  {simp only [function.iterate_succ', function.comp_app],
  obtain ⟨p,hn⟩:=hn,
  use ((-2*(C a)*X)*p+ p.derivative),
  intro x,
  have h₃:= funext hn, dsimp only at h₃, rw h₃,
  simp only [neg_mul, eval_add, eval_neg, eval_mul, eval_bit0, eval_one, eval_X],
  rw deriv_mul differentiable_at_complex_polynomial differentialbe_at_complex_exp,
  simp_rw ← neg_mul,
  rw [deriv_exp_neg_complex_mul_sq],
  simp only [polynomial.deriv, neg_mul, mul_neg],
  rw [add_mul, add_comm],
  simp only [eval_C, neg_mul],
  ring_nf,
  rw deriv_complex_polynomial,},
end


lemma mul_norm_add_le {a : ℝ} {b c : ℂ} (ha: 0 ≤ a): 
(a) * ‖b + c‖ ≤ (a) * ‖b‖ + (a) * ‖ c‖:= 
begin
  rw ←mul_add, 
  refine mul_le_mul rfl.ge (norm_add_le _ _) (norm_nonneg _) ha,
end


lemma polynomial_mul_exp_neg_sq_bounded (a : ℂ) (ha : 0<a.re): 
∀ p : polynomial ℂ, ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, 
‖x‖^k * ‖(λ (x : ℝ ), (p.eval x) * complex.exp (-a*x^2)) x‖ ≤ C :=
begin
  intro p,  intro k,  intro n,
  simp only [polynomial.eval_eq_sum_range],
  induction (p.nat_degree + 1) with j hj, 
  {use 0,  intro x,  rw [range_zero, sum_empty, zero_mul, complex.norm_eq_abs, absolute_value.map_zero, mul_zero],}, 
  rw [nat.succ_eq_one_add,add_comm],
  simp only [sum_range_succ,add_mul],
  obtain ⟨C_1,hj⟩:=hj,
  have h₁:= abs_pow_exp_neg_sq_bounded ha,
  obtain ⟨C_2,h₁⟩:=h₁,
  use (C_1 + ‖p.coeff j‖ * C_2),
  intro x,
  have h₁:= h₁ x,
  rw [complex.norm_eq_abs] at h₁ ,
  convert le_trans (mul_norm_add_le _) (add_le_add (hj x) _),
  positivity,
  simp only [norm_eq_abs, neg_mul, complex.norm_eq_abs, absolute_value.map_mul, complex.abs_pow, abs_of_real],
  ring_nf,
  rw [mul_comm, mul_comm (complex.abs (_)) (|x|^j), ← mul_assoc, ← mul_assoc, ← pow_add],
  refine mul_le_mul _ rfl.ge (norm_nonneg (coeff p j)) _,
  convert h₁,
  simp only [neg_mul, absolute_value.map_mul, complex.abs_pow, abs_of_real],
  rw mul_comm _ a,
  refine le_trans _ h₁,
  positivity,
end


lemma gaussian_decay (a : ℂ) (ha : 0 < a.re):  
∀ (k n : ℕ), ∃ (C : ℝ), ∀ (x : ℝ), 
‖x‖ ^ k * ‖iterated_fderiv ℝ n (λ (x : ℝ), complex.exp (-a * ↑x ^ 2)) x‖ ≤ C :=
begin
  intro k,  intro n,
  have h₁:=deriv_iterative_exp_neg_sq,
  specialize h₁ n,  specialize h₁ a,
  obtain ⟨p,h₁⟩:=h₁,
  have h₂:= polynomial_mul_exp_neg_sq_bounded a ha,
  specialize h₂ p,  specialize h₂ k,  specialize h₂ n,
  obtain ⟨C,h₂⟩:=h₂,
  use C, 
  intro x,
  rw [iterated_fderiv_eq_equiv_comp, iterated_deriv_eq_iterate,
  linear_isometry_equiv.norm_map,h₁ x],
  exact h₂ x,
end


def gaussian_complex {a : ℂ} (ha : 0 < a.re): schwartz_map ℝ ℂ :=
  { to_fun := λ x : ℝ, complex.exp (-a * x ^ 2),
    smooth':= by exact gaussian_smooth a,
    decay' := by exact gaussian_decay a ha}

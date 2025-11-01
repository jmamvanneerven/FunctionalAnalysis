import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

variable {𝕂 : Type _} {V : Type _} [RCLike 𝕂] [NormedAddCommGroup V] [NormedSpace 𝕂 V]

open Module

/-- Definition 1.32 -/
def norm_equiv (norm1 : V → ℝ) (norm2 : V → ℝ) : Prop :=
  ∃ c > 0, ∃ C ≥ c, ∀ x : V, c * norm1 x ≤ norm2 x ∧ norm2 x ≤ C * norm1 x


theorem norm_equiv_refl (n : V → ℝ) : norm_equiv n n := by
  exact ⟨1, by linarith, 1, by linarith, fun x => ⟨by linarith, by linarith⟩⟩

theorem norm_equiv_symm {n1 n2 : V → ℝ} (h : norm_equiv n1 n2) : norm_equiv n2 n1 := by
  rcases h with ⟨c, hc, C, hC, hnorms⟩
  use 1/C, by grind [one_div, inv_pos]
  use 1/c, by grind [one_div, inv_le_inv₀]
  intro x
  specialize hnorms x
  constructor
  · grind [one_div, inv_mul_le_iff₀]
  · simp_all
    grind [one_div, le_inv_mul_iff₀]

theorem norm_equiv_trans {n1 n2 n3 : V → ℝ}
  (h1 : norm_equiv n1 n2)
  (h2 : norm_equiv n2 n3) : norm_equiv n1 n3 := by
  rcases h1 with ⟨c1, hc1, C1, hC1, hnorms1⟩
  rcases h2 with ⟨c2, hc2, C2, hC2, hnorms2⟩
  use c1 * c2, by positivity
  use C1 * C2, by apply mul_le_mul_of_nonneg <;> grind
  intro x
  specialize hnorms1 x
  specialize hnorms2 x
  constructor
  · refine le_trans ?_ hnorms2.left
    grind [mul_assoc, mul_comm, mul_le_mul_iff_right₀]
  · refine le_trans hnorms2.right ?_
    grind [mul_assoc, mul_comm, mul_le_mul_iff_right₀]

/-- Theorem 1.34
 Two norms on a finite-dimensional vector space are equivalent
 This definition looks a bit wonky, because norms are typeclasses,
 so we take NormedAddCommGroup as parameters and construct the NormedSpace using that.
-/
theorem norm_equiv_of_finite_dimensional
  [FiniteDimensional 𝕂 V]
  (n1 : NormedAddCommGroup V)
  (n2 : NormedAddCommGroup V)
  (s1 : @NormedSpace 𝕂 V _ n1.toSeminormedAddCommGroup)
  (s2 : @NormedSpace 𝕂 V _ n2.toSeminormedAddCommGroup) :
  norm_equiv n1.norm n2.norm := by
  -- Obtain a basis for V
  let ι := Basis.ofVectorSpaceIndex 𝕂 V
  let basis : Basis ι 𝕂 V := Basis.ofVectorSpace 𝕂 V

  sorry

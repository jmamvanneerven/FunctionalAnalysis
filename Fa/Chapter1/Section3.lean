import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Seminorm
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Data.Real.Basic
import Fa.ForMathlib.Analysis.Seminorm
import Fa.Definitions.Definitions

variable {𝕂 : Type _} {V : Type _}

open Module

/-- Definition 1.32: two norms (as functions) are equivalent
if they bound each other up to positive constants. -/
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


theorem norm_equiv_equivalence : Equivalence (norm_equiv (V := V)) := by
  refine ⟨norm_equiv_refl (V := V), ?symm, ?trans⟩
  · intro n₁ n₂ h; exact norm_equiv_symm (V := V) h
  · intro n₁ n₂ n₃ h₁ h₂; exact norm_equiv_trans (V := V) h₁ h₂


-- structure Fa.Norm (𝕂 : Type _) (V : Type _) [RCLike 𝕂] where
--   nacg : NormedAddCommGroup V
--   ns : @NormedSpace 𝕂 V _ nacg.toSeminormedAddCommGroup

-- def Fa.Norm.norm (n : Fa.Norm 𝕂 V) : V → ℝ := n.nacg.norm

variable [RCLike 𝕂]
variable [nacg : NormedAddCommGroup V] [ns : NormedSpace 𝕂 V]
theorem norm_equiv_of_subsingleton [h : Subsingleton V]
  (norm1 : V → ℝ)
  (norm2 : V → ℝ)
  (h1 : norm1 0 = 0)
  (h2 : norm2 0 = 0) :
  norm_equiv norm1 norm2 := by
  use 1, by linarith
  use 1, by linarith
  intro x
  simp [Subsingleton.elim x 0, h1, h2]


noncomputable def euclidean_norm {ι : Type _} [Fintype ι] (b : Basis ι 𝕂 V) (v : V) : ℝ :=
    Real.sqrt (∑ i, ‖b.coord i v‖ ^ 2)

theorem norm_equiv_euclidean_of_finite_dimensional
  {ι : Type _}
  [Fintype ι]
  [FiniteDimensional 𝕂 V]
  (basis : Basis ι 𝕂 V)
  (n : Fa.Norm 𝕂 V)
  : norm_equiv n (euclidean_norm basis) := by

  by_cases hdim : Module.rank 𝕂 V = 0
  · rw [rank_zero_iff] at hdim
    exact norm_equiv_of_subsingleton n (euclidean_norm basis) (n.toSeminorm.map_zero')
      (by simp [euclidean_norm])
  -- Let M := max 1⩽j⩽d ∥x j∥.
  let M : ℝ := ((Finset.univ : Finset ι).image (fun i ↦ n (basis i))).max' (by
    apply Finset.image_nonempty.mpr
    rw [← Finset.card_ne_zero, Finset.card_univ]
    simpa [rank_eq_card_basis basis] using hdim
    )
  have hM0 : 0 ≤ M := by
    subst M
    refine le_trans ?_ (Finset.min'_le_max' _ _)
    apply Finset.le_min'
    intro y hy
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
    obtain ⟨a, rfl⟩ := hy
    apply apply_nonneg n.toSeminorm
  apply norm_equiv_symm

  let m : ℝ := sorry

  use m, sorry, M*√(Fintype.card ι), sorry
  intro x
  let c := basis.repr x

  have h0cs : 0 ≤ ∑ i, ‖c i‖ := by
    apply Fintype.sum_nonneg
    exact Pi.le_def.mpr (fun i ↦ by simp)

  constructor
  · sorry
  · calc
      n x ≤ ∑ i, ‖c i‖ * n (basis i) := by
        rw [← basis.sum_repr x]
        apply le_trans (n.sum_le _)
        rw [show n.toSeminorm = n.toSeminorm.toFun from rfl]
        conv =>
          lhs; enter [2, i]; rw [n.toSeminorm.smul']
        rfl
      _ ≤ M * ∑ i, ‖c i‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        have hnM : n (basis i) ≤ M := by
          exact (Finset.le_max' _ (n (basis i))
            (by rw [@mem_image_univ_iff_mem_range]; use i))

        have : 0 ≤ ‖c i‖ := by exact norm_nonneg (c i)
        rw [mul_comm]
        apply mul_le_mul hnM (by rfl) (norm_nonneg _)
        exact le_trans (apply_nonneg n.toSeminorm (basis i)) hnM
      _ ≤ M * √(Fintype.card ι) * √ (∑ i, ‖c i‖^2) := by
        rw [mul_assoc, ← Real.sqrt_mul (Nat.cast_nonneg' _)]
        refine mul_le_mul (by rfl) ?_ h0cs hM0
        have := @sq_sum_le_card_mul_sum_sq ι _ _ _ _ _ (Finset.univ) (fun i => ‖c i‖)
        rw [← Real.le_sqrt h0cs (by
          apply mul_nonneg (Nat.cast_nonneg' _)
          apply Fintype.sum_nonneg
          exact Pi.le_def.mpr (fun i ↦ by simp))] at this
        simpa using this
      _ = M * √(Fintype.card ι) * euclidean_norm basis x := by
        congr

/-- Theorem 1.34
 Two norms on a finite-dimensional vector space are equivalent
-/
theorem norm_equiv_of_finite_dimensional
  [h : FiniteDimensional 𝕂 V]
  (n1 : Fa.Norm 𝕂 V) (n2 : Fa.Norm 𝕂 V) :
  norm_equiv n1 n2 := by
  -- We define the euclidean norm
  let ι := Basis.ofVectorSpaceIndex 𝕂 V
  let basis : Basis ι 𝕂 V := Basis.ofVectorSpace 𝕂 V
  suffices ∀ (n : Fa.Norm 𝕂 V), norm_equiv n (euclidean_norm basis) by
    exact norm_equiv_trans (this n1) (norm_equiv_symm (this n2))
  apply norm_equiv_euclidean_of_finite_dimensional

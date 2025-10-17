import Mathlib

variable (𝕂 : Type _) (V : Type _) [AddCommGroup V] [RCLike 𝕂]

class VectorSpace extends Module 𝕂 V

@[ext]
class NormedSpace' [Norm V] extends VectorSpace 𝕂 V where
  zero_iff (v : V) : ‖v‖ = 0 ↔ v = 0
  scalar_hom (k : 𝕂) (v : V) : ‖k • v‖ = ‖k‖ * ‖v‖
  triangle_ineq (v w : V) : ‖v + w‖ ≤ ‖v‖ + ‖w‖

instance [Norm V] [NormedSpace' 𝕂 V] : SeminormedAddGroup V := by sorry
-- instance [Norm V] [NormedSpace' 𝕂 V] : NormedSpace 𝕂 V := by sorry

def normedSpace_equiv [h : NormedAddCommGroup V] : NormedSpace' 𝕂 V ≃ NormedSpace 𝕂 V where
  toFun v := {
    smul_zero := by
      haveI :=h.toSeminormedAddCommGroup.toAddCommGroup.toAddMonoid
      sorry
    smul_add := by sorry
    add_smul := by sorry
    zero_smul := by sorry
    norm_smul_le a b := le_of_eq (v.scalar_hom _ _)
  }

  invFun := sorry
  left_inv := sorry
  right_inv := sorry

class BanachSpace [NormedAddCommGroup V] [CompleteSpace V] extends NormedSpace' 𝕂 V


class InnerProductSpace' [NormedAddCommGroup V] extends VectorSpace 𝕂 V, Inner 𝕂 V where
  add_left (u v w : V) : inner (u + v) w = inner u w + inner v w
  add_right (u v w : V) : inner u (v + w) = inner u v + inner u w
  scalar_mul_left (u v : V) (k : 𝕂) : inner (k • u) v = k * inner u v
  scalar_mul_right (u v : V) (k : 𝕂) : inner u (k • u) = (starRingEnd 𝕂) k * inner u v
  nonneg (v : V) : RCLike.re (inner v v) ≥ 0 ∧ (starRingEnd 𝕂) (inner v v) = inner v v
  definite (v : V) : inner v v = 0 ↔ v = 0

structure IsLinearMap' {V : Type _} [AddCommGroup V] {W : Type _} [AddCommGroup W] [VectorSpace 𝕂 V]
    [VectorSpace 𝕂 W] (f : V → W) : Prop where
  add (v w : V) : f (v + w) = f v + f w
  mul (v : V) (k : 𝕂) : f (k • v) = k • f v


structure IsBoundedLinearMap' [Norm V]
    [NormedSpace' 𝕂 V] {W : Type _} [Norm W] [AddCommGroup W]
    [NormedSpace' 𝕂 W] (f : V → W) : Prop extends IsLinearMap' 𝕂 f where
  bound : ∃ M, 0 < M ∧ ∀ x : V, ‖f x‖ ≤ M * ‖x‖

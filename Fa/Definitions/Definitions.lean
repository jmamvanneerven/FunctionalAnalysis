import Mathlib

variable (𝕂 : Type _) (V : Type _) [RCLike 𝕂]

namespace Fa

class VectorSpace [AddCommGroup V] extends Module 𝕂 V


class NormedSpace [NormedAddCommGroup V] extends VectorSpace 𝕂 V where
  zero_iff (v : V) : ‖v‖ = 0 ↔ v = 0
  scalar_hom (k : 𝕂) (v : V) : ‖k • v‖ = ‖k‖ * ‖v‖
  triangle_ineq (v w : V) : ‖v + w‖ ≤ ‖v‖ + ‖w‖


def normedSpace_equiv [h : NormedAddCommGroup V] : NormedSpace 𝕂 V ≃ _root_.NormedSpace 𝕂 V where
  toFun ns' := {
    smul_zero := smul_zero
    smul_add := smul_add
    add_smul := add_smul
    zero_smul := zero_smul 𝕂
    norm_smul_le a b := le_of_eq (ns'.scalar_hom a b)
  }
  invFun ns := {
    zero_iff _ := norm_eq_zero
    scalar_hom := norm_smul
    triangle_ineq := norm_add_le
  }

instance [h : NormedAddCommGroup V] [h : NormedSpace 𝕂 V] : _root_.NormedSpace 𝕂 V :=
  (normedSpace_equiv _ _).toFun h

class BanachSpace [NormedAddCommGroup V] [CompleteSpace V] extends NormedSpace 𝕂 V


class InnerProductSpace [NormedAddCommGroup V] extends VectorSpace 𝕂 V, Inner 𝕂 V where
  add_left (u v w : V) : inner (u + v) w = inner u w + inner v w
  add_right (u v w : V) : inner u (v + w) = inner u v + inner u w
  scalar_mul_left (u v : V) (k : 𝕂) : inner (k • u) v = k * inner u v
  scalar_mul_right (u v : V) (k : 𝕂) : inner u (k • u) = (starRingEnd 𝕂) k * inner u v
  nonneg (v : V) : RCLike.re (inner v v) ≥ 0 ∧ (starRingEnd 𝕂) (inner v v) = inner v v
  definite (v : V) : inner v v = 0 ↔ v = 0
  norm_sq_eq_re_inner (v : V) : ‖v‖ ^ 2 = RCLike.re (inner v v)

def innerProductSpace_equiv [h : NormedAddCommGroup V] : InnerProductSpace 𝕂 V ≃ _root_.InnerProductSpace 𝕂 V := by
  -- Isomorphism requires swapping the order in inner product
  sorry

structure IsLinearMap' {V : Type _} [AddCommGroup V] {W : Type _} [AddCommGroup W] [VectorSpace 𝕂 V]
    [VectorSpace 𝕂 W] (f : V → W) : Prop where
  add (v w : V) : f (v + w) = f v + f w
  mul (v : V) (k : 𝕂) : f (k • v) = k • f v


structure IsBoundedLinearMap' [NormedAddCommGroup V] [NormedSpace 𝕂 V]
  {W : Type _} [NormedAddCommGroup W] [NormedSpace 𝕂 W] (f : V → W) : Prop extends IsLinearMap' 𝕂 f where
  bound : ∃ M, 0 < M ∧ ∀ x : V, ‖f x‖ ≤ M * ‖x‖

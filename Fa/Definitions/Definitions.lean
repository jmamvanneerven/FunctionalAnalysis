import Mathlib

variable (𝕂 : Type _) (V : Type _) [RCLike 𝕂]

namespace Fa

abbrev VectorSpace [AddCommGroup V] := Module 𝕂 V


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
  scalar_mul_right (u v : V) (k : 𝕂) : inner u (k • v) = (starRingEnd 𝕂) k * inner u v
  nonneg (v : V) : RCLike.re (inner v v) ≥ 0 ∧ (starRingEnd 𝕂) (inner v v) = inner v v
  definite (v : V) : inner v v = 0 ↔ v = 0
  conj_inner_symm (u v : V) : starRingEnd 𝕂 (inner u v) = inner v u
  norm_sq_eq_re_inner (v : V) : ‖v‖ ^ 2 = RCLike.re (inner v v)

lemma norm_smul_le [NormedAddCommGroup V] [ips : InnerProductSpace 𝕂 V] :
   ∀ (a : 𝕂) (b : V), ‖a • b‖ ≤ ‖a‖ * ‖b‖ := by
  intro a b
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [mul_pow, ips.norm_sq_eq_re_inner]
  rw [ips.norm_sq_eq_re_inner]
  rw [ips.scalar_mul_right, ips.scalar_mul_left]
  rw [@RCLike.norm_sq_eq_def_ax]
  simp
  ring_nf
  rfl

def innerProductSpace_equiv [h : NormedAddCommGroup V] : InnerProductSpace 𝕂 V ≃ _root_.InnerProductSpace 𝕂 V where
  toFun ips' := {
    toInner := {
      inner x y:= ips'.inner y x
    },
    norm_smul_le:= norm_smul_le _ _
    norm_sq_eq_re_inner := ips'.norm_sq_eq_re_inner
    conj_inner_symm := by simp [ips'.conj_inner_symm]
    add_left := by simp [ips'.add_right]
    smul_left := by simp [ips'.scalar_mul_right]
  }
  invFun ips := {
    toInner := {
      inner x y:= ips.inner y x
    },
    add_left := by simp [inner_add_right]
    add_right := by simp [inner_add_left]
    scalar_mul_left := by simp [inner_smul_right]
    scalar_mul_right := by simp [inner_smul_left]
    nonneg := by simp [inner_self_nonneg]
    definite := by simp
    norm_sq_eq_re_inner := by simp [inner_self_eq_norm_sq]
    conj_inner_symm := by simp
  }

structure IsLinearMap {V : Type _} [AddCommGroup V] {W : Type _} [AddCommGroup W] [VectorSpace 𝕂 V]
    [VectorSpace 𝕂 W] (f : V → W) : Prop where
  add (v w : V) : f (v + w) = f v + f w
  mul (k : 𝕂) (v : V) : f (k • v) = k • f v

def isLinearMap_iff {V : Type _} [AddCommGroup V] {W : Type _} [AddCommGroup W] [VectorSpace 𝕂 V]
    [VectorSpace 𝕂 W] (f : V → W) : IsLinearMap 𝕂 f ↔ _root_.IsLinearMap 𝕂 f := by
  refine ⟨fun h ↦ ⟨h.add, h.mul⟩, fun h ↦ ?_⟩
  exact ⟨h.map_add, h.map_smul⟩

structure IsBoundedLinearMap {V : Type _} [NormedAddCommGroup V] [NormedSpace 𝕂 V]
    {W : Type _} [NormedAddCommGroup W] [NormedSpace 𝕂 W]
    (f : V → W) : Prop extends IsLinearMap 𝕂 f where
  bound : ∃ M, 0 < M ∧ ∀ x : V, ‖f x‖ ≤ M * ‖x‖

def isBoundedLinearMap_iff [NormedAddCommGroup V] [NormedSpace 𝕂 V]
    {W : Type _} [NormedAddCommGroup W] [NormedSpace 𝕂 W] (f : V → W) :
  IsBoundedLinearMap 𝕂 f ↔ _root_.IsBoundedLinearMap 𝕂 f := by
  exact ⟨fun h ↦ ⟨(isLinearMap_iff _ _).mp h.toIsLinearMap, h.bound⟩,
    fun h ↦ ⟨(isLinearMap_iff _ _ ).mpr h.toIsLinearMap, h.bound⟩⟩

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Seminorm

variable {𝕂 : Type _} {V : Type _} [RCLike 𝕂] [NormedAddCommGroup V] [NormedSpace 𝕂 V]


open scoped BigOperators

lemma Seminorm.sum_le_finset {ι : Type _} [DecidableEq ι]
    (n : Seminorm 𝕂 V) (s : Finset ι) (f : ι → V) :
  n (∑ i ∈ s, f i) ≤ ∑ i ∈ s, n (f i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    -- rewrite the sum over insert
    have hadd : n (f a + ∑ i ∈ s, f i) ≤ n (f a) + n (∑ i ∈ s, f i) :=
      n.add_le' (f a) (∑ i ∈ s, f i)
    calc
      n (∑ i ∈ insert a s, f i)
          = n (f a + ∑ i ∈ s, f i) := by simp [Finset.sum_insert, ha]
      _ ≤ n (f a) + n (∑ i ∈ s, f i) := hadd
      _ ≤ n (f a) + ∑ i ∈ s, n (f i) := by
            exact add_le_add_left ih _
      _ = ∑ i ∈ insert a s, n (f i) := by simp [Finset.sum_insert, ha]

theorem Seminorm.sum_le {ι : Type _} [Fintype ι]
    (n : Seminorm 𝕂 V) (f : ι → V) :
  n (∑ i : ι, f i) ≤ ∑ i : ι, n (f i) := by
  classical
  simpa using (Seminorm.sum_le_finset (n := n) (s := Finset.univ) (f := f))

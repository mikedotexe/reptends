import Mathlib

/-! A retained expansion is data: a radix and an indexed coefficient stream.
Its real-valued evaluation is a separate map; the type does not identify streams
that evaluate to the same number. Coefficients need not be legal radix digits.
-/
namespace RetainedProgression

structure Expansion where
  radix : ℕ
  coefficient : ℕ → ℕ

def geometric (B c : ℕ) : Expansion := ⟨B, fun n => c ^ n⟩

noncomputable def Expansion.term (e : Expansion) (n : ℕ) : ℝ :=
  (e.coefficient n : ℝ) / (e.radix : ℝ) ^ (n + 1)

/-- Evaluation alone is meaningful for the intended infinite sum only with a
summability proof. The geometric family receives an explicit `HasSum` theorem. -/
noncomputable def Expansion.value (e : Expansion) : ℝ := ∑' n, e.term n

noncomputable def Expansion.partialValue (e : Expansion) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, e.term k

@[simp] theorem geometric_radix (B c : ℕ) : (geometric B c).radix = B := rfl
@[simp] theorem geometric_coefficient (B c n : ℕ) :
    (geometric B c).coefficient n = c ^ n := rfl

end RetainedProgression

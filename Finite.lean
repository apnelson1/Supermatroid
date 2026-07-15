import Supermatroid.Indep
import Supermatroid.Prelim.ENat
import Mathlib.Order.KrullDimension

open Order

variable {α : Type*} [Lattice α] {a b c x y z : α}

@[simps]
def LTSEries.map' {α β : Type*} [Preorder α] [Preorder β] (p : LTSeries α) (f : α → β)
    (hf : StrictMonoOn f {x | x ∈ p}) : LTSeries β where
      length := p.length
      toFun i := f (p i)
      step i := hf ⟨_, rfl⟩ ⟨_, rfl⟩ <| p.step i

lemma LTSeries.le_last_of_mem {α} [Preorder α] (p : LTSeries α) {a : α} (ha : a ∈ p) :
    a ≤ p.last := by
  obtain ⟨y, rfl : p.toFun y = a⟩ := by simpa only [RelSeries.mem_def, Set.mem_range] using ha
  exact p.monotone <| Fin.le_last y

lemma LTSeries.head_le_of_mem {α} [Preorder α] (p : LTSeries α) {a : α} (ha : a ∈ p) :
    p.head ≤ a := by
  obtain ⟨y, rfl : p.toFun y = a⟩ := by simpa only [RelSeries.mem_def, Set.mem_range] using ha
  exact p.monotone zero_le

@[simp]
lemma LTSeries.mem_eraseLast {α : Type*} [Preorder α] {p : LTSeries α} {a : α} (hp : p.length ≠ 0) :
    a ∈ p.eraseLast ↔ a ∈ p ∧ a ≠ p.last := by
  nth_rw 1 [iff_comm, ← p.snoc_self_eraseLast hp, RelSeries.mem_snoc, or_and_right,
    or_iff_left (by simp), and_iff_left_iff_imp]
  rintro ha rfl
  exact (LTSeries.le_last_of_mem _ ha).not_gt <| RelSeries.eraseLast_last_rel_last p hp

lemma CovBy.height_eq [IsLowerModularLattice α] {a b : α} (h : a ⋖ b) :
    Order.height b = Order.height a + 1 := by
  refine (height_add_one_le h.lt).antisymm' <| height_le_iff'.2 fun p hp ↦ ?_
  rw [← hp] at h
  by_cases hp0 : p.length = 0
  · simp [hp0]
  rw [← p.snoc_self_eraseLast hp0, RelSeries.snoc_length, Nat.cast_add, Nat.cast_one,
      ENat.add_one_le_add_one_iff]
  set z := p.eraseLast.last with hz
  by_cases hle : z ≤ a
  · grw [Order.length_le_height_last, ← hz, height_mono hle]
  obtain hza | hza := h.eq_or_eq (c := z ⊔ a) (by simp) (sup_le
    (p.le_last_of_mem <| by simp [hz, RelSeries.mem_def]) h.le)
  · simp [hle] at hza
  rw [← hza] at h
  have hc' := inf_covBy_of_covBy_sup_right h
  have hzza : z < z ⊔ a := hz ▸ hza ▸ p.eraseLast_last_rel_last hp0
  have hlt : z ⊓ a < a := by simpa [inf_lt_right] using hzza
  obtain htop | hlttop := eq_top_or_lt_top (height (z ⊓ a))
  · grw [← height_mono (show z ⊓ a ≤ a by simp), htop, ← le_top]
  have hlt' := height_strictMono hlt hlttop
  have ih := hc'.height_eq
  grw [← Order.add_one_le_of_lt hlt', ← ih, Order.length_le_height_last]
termination_by height a

class FiniteSupermatroid (α : Type*) [Lattice α] where
  /-- The relation of spanning from below, denoted `a ≤₀ b`. -/
  (SpansLE : α → α → Prop)
  /-- The relation of cospanning from below, denoted `a ≤₁ b`. -/
  (CospansLE : α → α → Prop)
  /-- `≤₀` implies `≤`, and `a ≤₀ b ≤₀ c ↔ a ≤₀ c` for all `b ∈ [a,c]`. -/
  (spansLE_refinement : StrongRefinement α SpansLE)
  /-- `≤₁` implies `≤`, and `a ≤₁ b ≤₁ c ↔ a ≤₁ c` for all `b ∈ [a,c]`. -/
  (cospansLE_refinement : StrongRefinement α CospansLE)
  /-- Every nonempty interval `[a,b]` contains some `x` with `a ≤₁ x ≤₀ b`. -/
  (spansLE_or_cospansLE_of_cover : ∀ a b, a ⋖ b → SpansLE a b ∨ CospansLE a b)
  (eq_of_diamond : ∀ a b b' c, a ⋖ b → a ⋖ b' → b ⋖ c → b' ⋖ c → SpansLE a b → SpansLE a b' →
    SpansLE b c → SpansLE b' c → b = b')
  -- (exists_rel_isBase : ∀ ⦃a b⦄, a ≤ b → ∃ x, CospansLE a x ∧ SpansLE x b)
  -- /-- There are no diamonds with spans below and cospans above -/
  -- (eq_of_diamond : ∀ ⦃a b⦄, SpansLE (a ⊓ b) a → SpansLE (a ⊓ b) b →
  --   CospansLE a (a ⊔ b) → CospansLE b (a ⊔ b) → a = b)
  -- /-- Some element is cospanned by everything below it. Only needed in unbounded lattices. -/
  -- (exists_indep' : ∃ i, ∀ x < i, CospansLE x i)
  -- /-- Some element spans everything above it. Only needed in unbounded lattices. -/
  -- (exists_spanning' : ∃ s, ∀ x > s, SpansLE s x)

-- example [BoundedOrder α] [ComplementedLattice α] [FiniteSupermatroid α] : Supermatroid α where
--   SpansLE := FiniteSupermatroid.SpansLE
--   CospansLE := FiniteSupermatroid.CospansLE
--   spansLE_refinement := _
--   cospansLE_refinement := _
--   exists_rel_isBase := _
--   eq_of_diamond := _
--   exists_indep' := _
--   exists_spanning' :=

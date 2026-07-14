import Mathlib.Order.Minimal
import LatticeMatroid.Supermatroid.Indep

/-
Here we give two alternative definitions for a `Supermatroid`.
The first `BaseSupermatroid`, is in terms of isBases, and has self-dual axioms.
They look a little strange, but in the finite setting they specialize
to the usual matroid axioms without too much work, and the self-duality saves a lot of time.

The second, `IndepSupermatroid`, is a set of independence axioms that readily
specializes to the familiar ones for both matroids and q-matroids.

We show that `IndepSupermatroid ⇒ BaseSupermatroid ⇒ Supermatroid`. The reverse
direction would take a little extra work but shouldn't be too hard.

Since we are making a beeline towards the definition of a `Supermatroid`,
we do not provide extensive API for `IndepSupermatroid` or `BaseSupermatroid`;
this will be inherited from the API for `Supermatroid`.
Despite this, I have tried not to make things too terse.
Some lemmas that turned out not to be needed are commented out. -/

open OrderDual

variable {α : Type*} {i j b x y z s t : α}

/-- A `BaseSupermatroid` is a supermatroid defined in terms of its isBases.
The axiom set is self-dual. -/
class BaseSupermatroid (α : Type*) [Lattice α] where
  /-- A `IsBase` predicate -/
  (IsBase : α → Prop)
  /-- Bases are an antichain -/
  (antichain : IsAntichain (· ≤ ·) (setOf IsBase))
  /-- There is a base. This is equivalent to the assertion that `α` is nonempty. -/
  (exists_isBase : ∃ b, IsBase b)
  /-- For all bases `b₁, b₂` and all `x₁, x₂`, the interval `[x₁ ⊓ b₁, x₂ ⊓ b₂]` contains a base. -/
  (exists_isBase_between_inf_sup :
    ∀ ⦃b₁ b₂ : α⦄, IsBase b₁ → IsBase b₂ → ∀ (x₁ x₂ : α),
      x₁ ⊓ b₁ ≤ x₂ ⊔ b₂ → ∃ b, IsBase b ∧ x₁ ⊓ b₁ ≤ b ∧ b ≤ x₂ ⊔ b₂)
  /-- `IsFrame b x` means that `b` is a isBase intersecting `x` in a isBasis for `x`.
    (This is not how we actually define it, but we'll prove it. ) -/
  (IsFrame : α → α → Prop)
  /-- We define `IsFrame b x` in a self-dual way.
  A isBase `b` is a `IsFrame` for `x` if every isBase `b'` in the interval `[x ⊓ b, x ⊔ b]`
  has the same sup and inf with `x` that `b` does. -/
  (isFrame_iff : ∀ ⦃b x⦄, IsFrame b x ↔ IsBase b ∧ ∀ b₁, IsBase b₁ → x ⊓ b ≤ b₁ → b₁ ≤ x ⊔ b →
    x ⊓ b₁ = x ⊓ b ∧ x ⊔ b₁ = x ⊔ b)
  /-- Every element has a isFrame. -/
  (exists_isFrame : ∀ x, ∃ b, IsFrame b x)
  /-- If `b` is a frame for `x` and `y` and `x,y` have the same inf and sup with `b`, then `x = y`.
  This encodes the 'no bad diamond' axiom that is typically needed for lattice definitions. -/
  (eq_of_isFrame_isFrame : ∀ ⦃x y b⦄, IsFrame b x → IsFrame b y →
    x ⊓ b = y ⊓ b → x ⊔ b = y ⊔ b → x = y)

namespace BaseSupermatroid

/-- A `BaseSupermatroid` gives a `BaseSupermatroid` on the dual lattice. This halves our work. -/
instance {α : Type*} [Lattice α] [BaseSupermatroid α] : BaseSupermatroid αᵒᵈ where
  IsBase b := IsBase <| ofDual b
  IsFrame b x := IsFrame (ofDual b) (ofDual x)
  exists_isBase := exists_isBase (α := α)
  isFrame_iff b x := by
    simp_rw [isFrame_iff, OrderDual.forall, ofDual_toDual, and_congr_right_iff]
    refine fun _ ↦ ⟨fun h b' hb' h1 h2 ↦ And.symm (h b' hb' h2 h1),
      fun h b' hb' h1 h2 ↦ And.symm (h b' hb' h2 h1)⟩
  antichain _ hb _ hb' hne := antichain (α := α) hb' hb hne.symm
  exists_isBase_between_inf_sup b₁ b₂ hb₁ hb₂ x₁ x₂ hle := by
    obtain ⟨b, hb, hleb, hble⟩ := exists_isBase_between_inf_sup (α := α) hb₂ hb₁ x₂ x₁ hle
    exact ⟨b, hb, hble, hleb⟩
  exists_isFrame x := exists_isFrame (ofDual x)
  eq_of_isFrame_isFrame x y b hx hy hi hu := (eq_of_isFrame_isFrame hy hx hu.symm hi.symm).symm

variable [Lattice α] [BaseSupermatroid α] {b' b₁ b₂ : α}

lemma IsBase.eq_of_le (hb : IsBase b) (hb' : IsBase b') (hle : b ≤ b') : b = b' :=
  antichain.eq hb hb' hle

lemma IsBase.toDual (h : IsBase b) : IsBase (toDual b) :=
  h

lemma IsBase.ofDual {b : αᵒᵈ} (h : IsBase b) : IsBase (ofDual b) :=
  h

@[simp] lemma isBase_dual_iff : IsBase (toDual b) ↔ IsBase b := Iff.rfl

lemma isFrame_def : IsFrame b x ↔ IsBase b ∧ ∀ b₁, IsBase b₁ → x ⊓ b ≤ b₁ → b₁ ≤ x ⊔ b →
    x ⊓ b₁ = x ⊓ b ∧ x ⊔ b₁ = x ⊔ b := by rw [isFrame_iff]

lemma IsFrame.ofDual {b x : αᵒᵈ} (h : IsFrame b x) : IsFrame (ofDual b) (ofDual x) :=
  h

lemma IsFrame.toDual (h : IsFrame b x) : IsFrame (toDual b) (toDual x) :=
  h

@[simp] lemma isFrame_dual_iff : IsFrame (toDual b) (toDual x) ↔ IsFrame b x := Iff.rfl

lemma IsFrame.isBase (h : IsFrame b x) : IsBase b :=
  (isFrame_def.1 h).1

lemma IsBase.isFrame_of_inf [IsModularLattice α] (hb : IsBase b)
    (h : ∀ b', IsBase b' → x ⊓ b ≤ b' → x ⊓ b' ≤ b) : IsFrame b x := by
  refine isFrame_def.2 ⟨hb, fun b₁ hb₁ hleb₁ hb₁le ↦ ?_⟩
  obtain ⟨b', hb', hleb', hb'le⟩ := exists_isBase_between_inf_sup hb hb₁ (x ⊔ b₁) x inf_le_left
  obtain rfl : (x ⊔ b₁) ⊓ b = b' := by
    apply eq_of_le_of_inf_le_of_le_sup (z := x) hleb'
    · have hxb'b := h b' hb' (le_trans (inf_le_inf_right _ le_sup_left) hleb')
      rwa [le_inf_iff, and_iff_right (inf_le_left.trans hb'le), inf_comm]
    rw [inf_sup_assoc_of_le _ le_sup_left, sup_comm b]
    exact le_inf hb'le (hb'le.trans (sup_le le_sup_left hb₁le))
  simp [le_antisymm_iff, hleb₁, hb₁le, show b ≤ x ⊔ b₁ by simpa using hb'.eq_of_le hb inf_le_right,
    h b₁ hb₁ hleb₁]

-- lemma IsBase.isFrame_of_sup (hb : IsBase b) (h : ∀ b', IsBase b' → b' ≤ x ⊔ b → b ≤ x ⊔ b') :
--     IsFrame b x :=
--   hb.toDual.isFrame_of_inf h

lemma IsFrame.inf_eq_inf (h : IsFrame b x) (hb' : IsBase b') (hle : x ⊓ b ≤ b') :
    x ⊓ b' = x ⊓ b := by
  suffices x ⊓ b' ≤ x ⊓ b by simpa [le_antisymm_iff, hle]
  obtain ⟨b₁, hb₁, hleb₁, hb₁le⟩ := exists_isBase_between_inf_sup hb' h.isBase (x ⊔ b) x inf_le_left
  obtain ⟨hi, hu⟩ := (isFrame_def.1 h).2 _ hb₁ ((le_inf inf_le_sup hle).trans hleb₁) hb₁le
  rw [← hi] at hle ⊢
  rw [← hu] at hleb₁
  exact le_inf inf_le_left <| (inf_le_inf_right _ le_sup_left).trans hleb₁

-- lemma IsFrame.sup_eq_sup (h : IsFrame b x) (hb' : IsBase b') (hle : b' ≤ x ⊔ b) :
--   x ⊔ b' = x ⊔ b :=
--   h.toDual.inf_eq_inf hb' hle

section Indep

/-- An `Indep`endent element is anything below a isBase. -/
def Indep (i : α) := ∃ b, IsBase b ∧ i ≤ b

/-- `IsBasis i x` means that `i` is a maximal independent element below `x`. -/
def IsBasis (i x : α) := Maximal (fun i ↦ Indep i ∧ i ≤ x) i

--  Indep i ∧ i ≤ x ∧ ∀ j, Indep j → i ≤ j → j ≤ x → i = j

lemma IsBasis.indep (h : IsBasis i x) : Indep i :=
  h.1.1

lemma IsBasis.le (h : IsBasis i x) : i ≤ x :=
  h.1.2

lemma IsBasis.eq_of_le (h : IsBasis i x) (hj : Indep j) (hij : i ≤ j) (hjx : j ≤ x) : i = j :=
  Maximal.eq_of_le h ⟨hj, hjx⟩ hij

  -- /h.2.2 j hj hij hjx

/-- A `Spanning` element is anything above a isBase. -/
def Spanning (s : α) := ∃ b, IsBase b ∧ b ≤ s

/-- `Canopy s x` means that `s` is a minimal spanning element above `x` -/
def Canopy (s x : α) := Minimal (fun s ↦ Spanning s ∧ x ≤ s) s

lemma Indep.mono (hi : Indep i) (hji : j ≤ i) : Indep j :=
  let ⟨b, hb, hib⟩ := hi
  ⟨b, hb, hji.trans hib⟩

lemma Spanning.mono (hs : Spanning s) (hst : s ≤ t) : Spanning t :=
  Indep.mono (α := αᵒᵈ) hs hst

lemma IsBase.indep (hb : IsBase b) : Indep b :=
  ⟨b, hb, rfl.le⟩

lemma IsBase.inf_indep (hb : IsBase b) : Indep (x ⊓ b) :=
  hb.indep.mono inf_le_right

lemma IsBase.spanning (hb : IsBase b) : Spanning b :=
  ⟨b, hb, rfl.le⟩

lemma Indep.exists_isBase_between_of_spanning (hi : Indep i) (hs : Spanning s) (his : i ≤ s) :
    ∃ b, IsBase b ∧ i ≤ b ∧ b ≤ s := by
  obtain ⟨b₁, hb₁, hib₁⟩ := hi
  obtain ⟨b₂, hb₂, hb₂s⟩ := hs
  obtain ⟨b, hb, hleb, hble⟩ := exists_isBase_between_inf_sup hb₁ hb₂ i s
    (inf_le_left.trans (his.trans le_sup_left))
  exact ⟨b, hb, by rwa [← inf_of_le_left hib₁], by rwa [← sup_of_le_left hb₂s]⟩

lemma Indep.exists_le_isBase_le_sup_isBase (hi : Indep i) (hb : IsBase b) :
    ∃ b', IsBase b' ∧ i ≤ b' ∧ b' ≤ i ⊔ b := by
  obtain ⟨b₁, hb₁, hib₁⟩ := hi
  obtain ⟨b', hb', hleb', hb'le⟩ :=
    exists_isBase_between_inf_sup hb₁ hb i i (inf_le_left.trans le_sup_left)
  exact ⟨b', hb', by rwa [← inf_of_le_left hib₁], hb'le⟩

lemma isBase_iff_indep_spanning : IsBase b ↔ Indep b ∧ Spanning b := by
  refine ⟨fun h ↦ ⟨h.indep, h.spanning⟩, fun ⟨hi, hs⟩ ↦ ?_⟩
  obtain ⟨b', hb', hleb', hb'le⟩ := hi.exists_isBase_between_of_spanning hs rfl.le
  rwa [← hb'le.antisymm hleb']

lemma Indep.isBasis_self (hi : Indep i) : IsBasis i i :=
  ⟨⟨hi, rfl.le⟩, by simp +contextual⟩

-- @[simp] lemma toDual_indep_iff : Indep (toDual s) ↔ Spanning s := Iff.rfl

-- @[simp] lemma toDual_spanning_iff : Spanning (toDual i) ↔ Indep i := Iff.rfl

-- @[simp] lemma toDual_canopy_iff : Canopy (toDual i) (toDual x) ↔ IsBasis i x := Iff.rfl

-- @[simp] lemma toDual_isBasis_iff : IsBasis (toDual s) (toDual x) ↔ Canopy s x := Iff.rfl

lemma IsFrame.inf_isBasis (h : IsFrame b x) : IsBasis (x ⊓ b) x := by
  refine ⟨⟨h.isBase.inf_indep, inf_le_left⟩, fun j hj hlej ↦ ?_⟩
  obtain ⟨b', hb', hjb', hb'j⟩ := hj.1.exists_le_isBase_le_sup_isBase h.isBase
  rwa [← h.inf_eq_inf hb' (hlej.trans hjb'), le_inf_iff, and_iff_right hj.2]

lemma IsFrame.sup_canopy (h : IsFrame b x) : Canopy (x ⊔ b) x :=
  h.toDual.inf_isBasis

lemma exists_isBasis (x : α) : ∃ i, IsBasis i x :=
  ⟨_, (exists_isFrame x).choose_spec.inf_isBasis⟩

variable [IsModularLattice α]

lemma IsBase.isFrame_iff_inf_isBasis (hb : IsBase b) : IsFrame b x ↔ IsBasis (x ⊓ b) x :=
  ⟨IsFrame.inf_isBasis, fun h ↦ hb.isFrame_of_inf fun b' hb' hleb' ↦ by
    simp [← h.eq_of_le (hb'.inf_indep) (le_inf inf_le_left hleb') inf_le_left]⟩

-- lemma IsBase.isFrame_iff_sup_canopy (hb : IsBase b) : IsFrame b x ↔ Canopy (x ⊔ b) x :=
--   hb.toDual.isFrame_iff_inf_isBasis

lemma IsBasis.exists_isFrame_eq_inf (hix : IsBasis i x) : ∃ b, IsFrame b x ∧ i = x ⊓ b := by
  obtain ⟨b, hb, hib⟩ := hix.indep
  obtain rfl := hix.eq_of_le (hb.inf_indep) (le_inf hix.le hib) inf_le_left
  rw [← hb.isFrame_iff_inf_isBasis] at hix
  exact ⟨b, hix, rfl⟩

lemma IsFrame.switch_of_inf (h : IsFrame b x) (hb' : IsBase b') (hle : x ⊓ b ≤ b') :
    IsFrame b' x := by
  rwa [hb'.isFrame_iff_inf_isBasis, h.inf_eq_inf hb' hle, ← h.isBase.isFrame_iff_inf_isBasis]

lemma IsFrame.switch_of_sup (h : IsFrame b x) (hb' : IsBase b') (hle : b' ≤ x ⊔ b) : IsFrame b' x :=
  h.toDual.switch_of_inf hb' hle

-- lemma exists_canopy (x : α) : ∃ s, Canopy s x :=
--   exists_isBasis <| toDual x

lemma exists_isFrame_isFrame_of_le (hxy : x ≤ y) : ∃ b, IsFrame b x ∧ IsFrame b y := by
  obtain ⟨b₁, hb₁⟩ := exists_isFrame x
  obtain ⟨b₂, hb₂⟩ := exists_isFrame y
  obtain ⟨b, hb, hleb, hble⟩ := exists_isBase_between_inf_sup hb₁.isBase hb₂.isBase x (x ⊓ b₁)
    le_sup_left
  refine ⟨b, hb₁.switch_of_inf hb hleb, hb₂.switch_of_sup hb <| hble.trans ?_⟩
  exact sup_le_sup_right (inf_le_left.trans hxy) _

theorem Indep.le_isBasis_le_sup (hi : Indep i) (hjx : IsBasis j x) (hix : i ≤ x) :
    ∃ k, IsBasis k x ∧ i ≤ k ∧ k ≤ i ⊔ j := by
  obtain ⟨b, hb, rfl⟩ := hjx.exists_isFrame_eq_inf
  obtain ⟨b', hb', hib', hb's⟩ := hi.exists_isBase_between_of_spanning (s := i ⊔ b)
    (hb.isBase.spanning.mono le_sup_right) le_sup_left
  refine ⟨x ⊓ b', IsFrame.inf_isBasis ?_, le_inf hix hib', ?_⟩
  · exact hb.switch_of_sup hb' <| hb's.trans (sup_le_sup_right hix _)
  rw [sup_comm, inf_sup_assoc_of_le _ hix, sup_comm]
  exact inf_le_inf_left _ hb's

end Indep

section Span

/-- `SpansLE x y` means that `x ≤ y` and every isBasis for `x` is a isBasis for `y`.
This is the `≤₀` relation in the associated supermatroid. -/
def SpansLE (x y : α) := x ≤ y ∧ ∀ i, IsBasis i x → IsBasis i y

/-- `CospansLE x y` means that `x ≤ y` and every canopy for `y` is a canopy for `x`.
This is the `≤₁` relation in the associated supermatroid, defined as the dual of `SpansLE`. -/
def CospansLE (x y : α) := SpansLE (toDual y) (toDual x)
-- x ≤ y ∧ ∀ s, Canopy s y → Canopy s x

@[simp] lemma SpansLE.refl : SpansLE x x := ⟨rfl.le, by simp⟩

@[simp] lemma CospansLE.refl : CospansLE x x := ⟨rfl.le, by simp⟩

-- @[simp] lemma cospansLE_dual_iff : CospansLE (toDual x) (toDual y) ↔ SpansLE y x := Iff.rfl

-- @[simp] lemma spansLE_dual_iff : SpansLE (toDual x) (toDual y) ↔ CospansLE y x := Iff.rfl

lemma IsBasis.spansLE (h : IsBasis i x) : SpansLE i x :=
  ⟨h.le, fun j hji ↦ by rwa [hji.eq_of_le h.indep hji.le rfl.le]⟩

lemma SpansLE.inf_eq_inf_of_isFrame (hxy : SpansLE x y) (hb : IsFrame b x) : y ⊓ b = x ⊓ b := by
  simp [← (hxy.2 _ hb.inf_isBasis).eq_of_le (hb.isBase.inf_indep)
    (inf_le_inf_right _ hxy.1) inf_le_left]

lemma Canopy.cospansLE (h : Canopy s x) : CospansLE x s :=
  IsBasis.spansLE (α := αᵒᵈ) h

lemma CospansLE.sup_eq_sup_of_isFrame (hxy : CospansLE x y) (hb : IsFrame b y) : x ⊔ b = y ⊔ b :=
  SpansLE.inf_eq_inf_of_isFrame (α := αᵒᵈ) hxy hb

variable [IsModularLattice α]

theorem spansLE_strongRefinement : StrongRefinement α SpansLE := by
  refine ⟨fun _ _ h ↦ h.1, fun x y z hxy hyz ↦
    ⟨fun ⟨_, h⟩ ↦ ⟨⟨hxy, fun i hi ↦ ?_⟩, ⟨hyz, fun i hi ↦ ?_⟩⟩,
    fun ⟨h,h'⟩ ↦ ⟨hxy.trans hyz, fun i hi ↦ h'.2 _ <| h.2 i hi⟩⟩⟩
  · exact ⟨⟨hi.indep, hi.le.trans hxy⟩,
      fun j hj hij ↦ ((h i hi).eq_of_le hj.1 hij (hj.2.trans hyz)).ge⟩
  obtain ⟨j, hj⟩ := exists_isBasis x
  obtain ⟨k, hk, hik, hkij⟩ := hi.indep.le_isBasis_le_sup (h _ hj) (hi.le.trans hyz)
  rwa [hi.eq_of_le hk.indep hik (hkij.trans <| sup_le hi.le <| hj.le.trans hxy)]

theorem cospansLE_strongRefinement : StrongRefinement α CospansLE :=
  (spansLE_strongRefinement (α := αᵒᵈ)).strongRefinement_ofDual

theorem exists_rel_isBase {c d : α} (hcd : c ≤ d) : ∃ x, CospansLE c x ∧ SpansLE x d := by
  obtain ⟨b, hbc, hbd⟩ := exists_isFrame_isFrame_of_le hcd
  refine ⟨(d ⊓ b) ⊔ c, ?_, ?_⟩
  · refine cospansLE_strongRefinement.rel_left_of_rel hbc.sup_canopy.cospansLE le_sup_right ?_
    simp [show d ⊓ b ≤ c ⊔ b from inf_le_right.trans le_sup_right]
  exact spansLE_strongRefinement.rel_right_of_rel hbd.inf_isBasis.spansLE (by simp)
    <| by simp [inf_sup_assoc_of_le _ hcd]

lemma SpansLE.isFrame_of_isFrame (hxy : SpansLE x y) (hb : IsFrame b x) : IsFrame b y := by
  rw [hb.isBase.isFrame_iff_inf_isBasis, hxy.inf_eq_inf_of_isFrame hb]
  exact (hxy.2 _ hb.inf_isBasis)

lemma CospansLE.isFrame_of_isFrame (hxy : CospansLE x y) (hb : IsFrame b y) : IsFrame b x :=
    SpansLE.isFrame_of_isFrame (α := αᵒᵈ) hxy hb

lemma eq_of_diamond (hix : SpansLE (x ⊓ y) x) (hiy : SpansLE (x ⊓ y) y)
    (hxu : CospansLE x (x ⊔ y)) (hyu : CospansLE y (x ⊔ y)) : x = y := by
  obtain ⟨b, hbi, hbu⟩ := exists_isFrame_isFrame_of_le (show x ⊓ y ≤ x ⊔ y from inf_le_sup)
  have hbx := hix.isFrame_of_isFrame hbi
  have hby := hiy.isFrame_of_isFrame hbi
  apply eq_of_isFrame_isFrame hbx hby
  · rw [hix.inf_eq_inf_of_isFrame hbi, hiy.inf_eq_inf_of_isFrame hbi]
  rw [hxu.sup_eq_sup_of_isFrame hbu, hyu.sup_eq_sup_of_isFrame hbu]

lemma SpansLE.eq_of_cospansLE (h₀ : SpansLE x y) (h₁ : CospansLE x y) : x = y := by
  simpa [inf_of_le_left h₀.1, h₀, sup_of_le_right h₀.1, h₁] using eq_of_diamond (x := x) (y := y)

lemma Indep.cospansLE_of_le (hi : Indep i) (hji : j ≤ i) : CospansLE j i := by
  obtain ⟨b, hbj, hbi⟩ := exists_rel_isBase hji
  rwa [← (hbi.2 _ (hi.mono hbi.1).isBasis_self).eq_of_le hi hbi.1 rfl.le]

lemma indep_iff_forall_cospansLE : Indep i ↔ ∀ ⦃j⦄, j ≤ i → CospansLE j i := by
  refine ⟨fun h _ ↦ h.cospansLE_of_le, fun h ↦ ?_⟩
  obtain ⟨b, hb⟩ := exists_isBasis i
  rw [← hb.spansLE.eq_of_cospansLE (h hb.le)]
  exact hb.indep

lemma Spanning.spansLE_of_le (hs : Spanning s) (hst : s ≤ t) : SpansLE s t :=
  Indep.cospansLE_of_le (α := αᵒᵈ) hs hst

lemma spanning_iff_forall_spansLE : Spanning s ↔ ∀ ⦃t⦄, s ≤ t → SpansLE s t :=
  indep_iff_forall_cospansLE (α := αᵒᵈ)

end Span
section Supermatroid

/-- A `BaseSupermatroid` gives a `Supermatroid`. -/
instance toSupermatroid (α : Type*) [Lattice α] [IsModularLattice α] [BaseSupermatroid α] :
    Supermatroid α where
  SpansLE := SpansLE
  CospansLE := CospansLE
  spansLE_refinement := spansLE_strongRefinement
  cospansLE_refinement := cospansLE_strongRefinement
  exists_rel_isBase _ _ := exists_rel_isBase
  eq_of_diamond _ _ := eq_of_diamond
  exists_indep' := ⟨_, fun _ h ↦ exists_isBase.choose_spec.indep.cospansLE_of_le h.le⟩
  exists_spanning' := ⟨_, fun _ h ↦ exists_isBase.choose_spec.spanning.spansLE_of_le h.le⟩

-- lemma toSupermatroid_spansLE_iff : x ≤₀ y ↔ SpansLE x y := Iff.rfl
-- lemma toSupermatroid_cospansLE_iff : x ≤₁ y ↔ CospansLE x y := Iff.rfl

variable [IsModularLattice α]

@[simp]
lemma toSupermatroid_indep_iff : Supermatroid.Indep i ↔ Indep i := by
  simp_rw [indep_iff_forall_cospansLE, Supermatroid.indep_iff_forall_cospansLE]; rfl

@[simp]
lemma toSupermatroid_spanning_iff : Supermatroid.Spanning s ↔ Spanning s :=
  toSupermatroid_indep_iff (α := αᵒᵈ)

@[simp]
lemma toSupermatroid_isBase_iff : Supermatroid.IsBase b ↔ IsBase b := by
  simp [Supermatroid.isBase_def, isBase_iff_indep_spanning]

@[simp]
lemma toSupermatroid_isBasis_iff : Supermatroid.IsBasis i x ↔ IsBasis i x := by
  simp [Supermatroid.isBasis_iff_maximal_indep, IsBasis]

end Supermatroid

end BaseSupermatroid

/-- A definition of a `Supermatroid` via its independent elements and isBasis predicate.
We assume the lattice has a maximum element `⊤`; this is needed to make a base exist.
(If we didn't include this assumption, we would get bad examples like where the
lattice comprises all finite sets and everything is independent.) -/
class IndepSupermatroid (α : Type*) [Lattice α] [OrderTop α] where
  /-- An independence predicate -/
  (Indep : α → Prop)
  /-- A isBasis predicate -/
  (IsBasis : α → α → Prop)
  /-- `IsBasis i x` means that `i` is a maximal independent element below `x`. -/
  (isBasis_iff : ∀ ⦃i x⦄, IsBasis i x ↔ Maximal (fun i ↦ Indep i ∧ i ≤ x) i)
  /-- There exists an independent element -/
  (exists_indep : ∃ i, Indep i)
  /-- Independence is monotone -/
  (indep_of_le : ∀ ⦃i j⦄, Indep j → i ≤ j → Indep i)
  /-- A nonmaximal independent element augments into its join with a maximal one -/
  (indep_augment : ∀ ⦃i b⦄, Indep i → ¬ IsBasis i ⊤ → IsBasis b ⊤ →
    ∃ j, Indep j ∧ i < j ∧ j ≤ i ⊔ b)
  /-- Every independent element below `x` is below a basis for `x`. -/
  (exists_le_isBasis_of_indep_le : ∀ i x, i ≤ x → Indep i → ∃ j, IsBasis j x ∧ i ≤ j)
  /-- A basis for two elements is a basis for their join. -/
  (isBasis_sup_of_isBasis_isBasis : ∀ ⦃i x y⦄, IsBasis i x → IsBasis i y → IsBasis i (x ⊔ y))

namespace IndepSupermatroid

variable [Lattice α] [OrderTop α] [IndepSupermatroid α]

lemma IsBasis.indep (h : IsBasis i x) : Indep i :=
  (isBasis_iff.1 h).1.1

lemma IsBasis.le (h : IsBasis i x) : i ≤ x :=
  (isBasis_iff.1 h).1.2

lemma IsBasis.eq_of_le (h : IsBasis i x) (hj : Indep j) (hij : i ≤ j) (hjx : j ≤ x) : i = j :=
  hij.antisymm <| (isBasis_iff.1 h).2 ⟨hj, hjx⟩ hij

lemma Indep.isBasis_of_forall (hi : Indep i) (hix : i ≤ x)
    (h : ∀ j, Indep j → i ≤ j → j ≤ x → i = j) : IsBasis i x :=
  isBasis_iff.2 ⟨⟨hi, hix⟩, fun j ⟨hj, hjx⟩ hij ↦ (h j hj hij hjx).symm.le⟩

lemma Indep.exists_le_isBasis (hi : Indep i) (hix : i ≤ x) : ∃ j, IsBasis j x ∧ i ≤ j :=
  exists_le_isBasis_of_indep_le _ _ hix hi

lemma Indep.mono (hj : Indep j) (hij : i ≤ j) : Indep i :=
  indep_of_le hj hij

lemma exists_isBasis (x : α) : ∃ i, IsBasis i x := by
  obtain ⟨j, hj⟩ := exists_indep (α := α)
  obtain ⟨i, hi, -⟩ := (hj.mono <| inf_le_left (b := x)).exists_le_isBasis inf_le_right
  exact ⟨i, hi⟩

abbrev IsBase (b : α) := IsBasis b ⊤

lemma IsBase.eq_of_le_indep (hb : IsBase b) (hi : Indep i) (hbi : b ≤ i) : b = i :=
  IsBasis.eq_of_le hb hi hbi le_top

lemma IsBase.indep (hb : IsBase b) : Indep b :=
  IsBasis.indep hb

lemma IsBasis.inf_indep (hb : IsBase b) : Indep (x ⊓ b) :=
  hb.indep.mono inf_le_right

lemma isBase_antichain : IsAntichain (· ≤ ·) {b : α | IsBase b} :=
  fun _ hb _ hb' hne hle ↦ hne <| (IsBase.eq_of_le_indep hb hb'.indep hle)

lemma Indep.exists_le_isBase (hi : Indep i) : ∃ b, IsBase b ∧ i ≤ b :=
  hi.exists_le_isBasis le_top

lemma exists_isBase : ∃ (b : α), IsBase b := by
  obtain ⟨i, hi⟩ := exists_indep (α := α)
  obtain ⟨b, hb, -⟩ := hi.exists_le_isBase
  exact ⟨b, hb⟩

lemma IsBase.isBase_of_isBasis_sup (hb : IsBase b) (hb' : IsBasis b' (x ⊔ b)) : IsBase b' := by
  refine hb'.indep.isBasis_of_forall le_top fun j hj hb'j _ ↦ by_contra fun hne ↦ ?_
  have hlt := hb'j.lt_of_ne hne
  have hnot : ¬ IsBasis b' ⊤ := fun hbas ↦ by simp [hbas.eq_of_le hj hlt.le le_top] at hlt
  obtain ⟨k, hk, hltk, hkle⟩ := indep_augment hb'.indep hnot hb
  obtain rfl : b' = k := hb'.eq_of_le hk hltk.le (hkle.trans (sup_le hb'.le le_sup_right))
  exact hltk.ne rfl

lemma exists_isBase_between_inf_sup (hb₁ : IsBase b₁) (hb₂ : IsBase b₂) (x₁ x₂ : α)
    (hle : x₁ ⊓ b₁ ≤ x₂ ⊔ b₂) : ∃ b, IsBase b ∧ x₁ ⊓ b₁ ≤ b ∧ b ≤ x₂ ⊔ b₂ := by
  have hxb₁ : Indep (x₁ ⊓ b₁) := hb₁.inf_indep
  obtain ⟨b, hb, hleb⟩ := hxb₁.exists_le_isBasis hle
  exact ⟨b,  hb₂.isBase_of_isBasis_sup hb, hleb, hb.le⟩

/-- `IsFrame b x` means that `b` is a isBase intersecting `x` in a isBasis. The hard part is showing
that that is the same definition that a `BaseSupermatroid` requires. -/
def IsFrame (b x : α) := IsBase b ∧ IsBasis (x ⊓ b) x

lemma exists_isFrame (x : α) : ∃ b, IsFrame b x := by
  obtain ⟨i, hi⟩ := exists_isBasis x
  obtain ⟨b, hb, hib⟩ := hi.indep.exists_le_isBase
  obtain rfl := hi.eq_of_le (hb.inf_indep) (le_inf hi.le hib) inf_le_left
  exact ⟨b, hb, hi⟩

variable [IsModularLattice α]

lemma isFrame_iff : IsFrame b x ↔ IsBase b ∧ ∀ b₁, IsBase b₁ → x ⊓ b ≤ b₁ → b₁ ≤ x ⊔ b →
    x ⊓ b₁ = x ⊓ b ∧ x ⊔ b₁ = x ⊔ b := by
  rw [IsFrame, and_congr_right_iff]
  refine fun hb ↦ ⟨fun h b₁ hb₁ hleb₁ hb₁le ↦ ?_, ?_⟩
  · rw [← h.eq_of_le (hb₁.inf_indep) (le_inf inf_le_left hleb₁) inf_le_left]
    suffices b ≤ x ⊔ b₁ by simpa [le_antisymm_iff, hb₁le]
    obtain ⟨b₂, hb₂', hib₂ : (x ⊔ b₁) ⊓ b ≤ b₂⟩ := hb.inf_indep.exists_le_isBasis inf_le_left
    have hb₂ : IsBase b₂ := hb₁.isBase_of_isBasis_sup hb₂'
    have h_eq : (x ⊔ b₁) ⊓ b = b₂ := eq_of_le_of_inf_le_of_le_sup hib₂ (z := x) ?_ ?_
    · rw [← hb₂.eq_of_le_indep hb.indep (by simp [← h_eq]), ← h_eq]
      exact inf_le_left
    · rw [inf_comm, ← h.eq_of_le hb₂.inf_indep (le_inf _ (le_trans _ hib₂))] <;>
      simp [inf_le_inf_right b (show x ≤ x ⊔ b₁ from le_sup_left)]
    rw [inf_sup_assoc_of_le _ le_sup_left, sup_comm b]
    refine le_inf ?_ (hb₂'.le.trans ?_) <;> simp [hb₂'.le, hb₁le]
  refine fun h ↦ (hb.inf_indep).isBasis_of_forall inf_le_left fun j hj hxbj hjx ↦ ?_
  obtain ⟨b', hb', hjb'⟩ := hj.exists_le_isBasis (hjx.trans (le_sup_left (b := b)))
  rw [le_antisymm_iff, and_iff_right hxbj,
    ← (h b' (hb.isBase_of_isBasis_sup hb') (hxbj.trans hjb') hb'.le).1]
  exact le_inf hjx hjb'

/-- If `b` is a frame for both `x` and `y`, and `b` has the same infinimum and supremum with
both `x` and `y`, then `x = y`. -/
lemma IsFrame.eq_of_isFrame_of_inf_eq_of_sup_eq (hx : IsFrame b x) (hy : IsFrame b y)
    (hi : x ⊓ b = y ⊓ b) (hu : x ⊔ b = y ⊔ b) : x = y := by
  have hbu := isBasis_sup_of_isBasis_isBasis hx.2 (hi.symm ▸ hy.2)
  rw [le_antisymm_iff, ← sup_eq_right, ← sup_eq_left, eq_comm, eq_comm (b := x)]
  refine ⟨eq_of_le_of_inf_le_of_sup_le le_sup_right (z := b) (Eq.symm ?_).le ?_,
    eq_of_le_of_inf_le_of_sup_le le_sup_left (z := b) (Eq.symm ?_).le ?_⟩
  · exact (hi ▸ hbu).eq_of_le hx.1.inf_indep (inf_le_inf_right _ le_sup_right) inf_le_left
  · rw [sup_assoc, ← hu, ← sup_assoc, sup_idem]
  · refine hbu.eq_of_le hx.1.inf_indep (inf_le_inf_right _ le_sup_left) inf_le_left
  rw [sup_assoc, ← hu, ← sup_assoc, sup_idem]

/-- An `IndepSupermatroid` determines a `BaseSupermatroid` (and hence a `Supermatroid`). -/
instance toBaseSupermatroid : BaseSupermatroid α where
  IsBase := IsBase
  antichain := isBase_antichain
  exists_isBase := exists_isBase
  exists_isBase_between_inf_sup _ _ := exists_isBase_between_inf_sup
  IsFrame := IsFrame
  isFrame_iff _ _ := isFrame_iff
  exists_isFrame := exists_isFrame
  eq_of_isFrame_isFrame _ _ _ := IsFrame.eq_of_isFrame_of_inf_eq_of_sup_eq

@[simp] lemma toBaseSupermatroid_isBase_iff : BaseSupermatroid.IsBase b ↔ IsBase b := Iff.rfl

@[simp] lemma toBaseSupermatroid_isFrame_iff : BaseSupermatroid.IsFrame b x ↔ IsFrame b x := Iff.rfl

@[simp] lemma toBaseSupermatroid_indep_iff : BaseSupermatroid.Indep i ↔ Indep i :=
  ⟨fun ⟨_, hb, hib⟩ ↦ (IsBase.indep hb).mono hib, Indep.exists_le_isBase⟩

@[simp] lemma toBaseSupermatroid_isBasis_iff : BaseSupermatroid.IsBasis i x ↔ IsBasis i x := by
  simp only [BaseSupermatroid.IsBasis, toBaseSupermatroid_indep_iff, isBasis_iff,
    maximal_iff, and_assoc]

end IndepSupermatroid

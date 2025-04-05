import Mathlib

/- Current attempts at defining the basic objects of study. Everything very subject to change. -/

noncomputable section

open Order Set

def SIdeal (α : Type*) := Order.Ideal (Set α)

instance {α : Type*} : SetLike (SIdeal α) (Set α) where
  coe := fun a ↦ a.carrier
  coe_injective' := by
    intro a b h
    simp at h
    exact h

section SIdealBasic

variable {α : Type*} {I : SIdeal α} {a b : Set α}

theorem SIdeal.empty_mem : ∅ ∈ I := sorry

theorem SIdeal.subset_mem (ha : b ∈ I) (h : a ⊆ b) : a ∈ I := I.lower h ha

theorem SIdeal.union_mem (ha : a ∈ I) (hb : b ∈ I) : a ∪ b ∈ I := by
  obtain ⟨z, hz⟩ := I.directed a ha b hb
  apply I.subset_mem hz.1
  exact union_subset hz.2.1 hz.2.2

end SIdealBasic

namespace Order

/- Not sure if these definitions and `<(f, g)` notations are helpful or obfuscating.
`lt_SIdeal` etc. can also just be defined directly. -/
def ltSet {L A : Type*} [LinearOrder L] (f g : A → L) : Set A :=
  {x | f x < g x}

def leSet {L A : Type*} [LinearOrder L] (f g : A → L) : Set A :=
  {x | f x ≤ g x}

def eqSet {L A : Type*} [LinearOrder L] (f g : A → L) : Set A :=
  {x | f x = g x}

def neSet {L A : Type*} [LinearOrder L] (f g : A → L) : Set A :=
  {x | f x ≠ g x}

notation "<(" f:50 ", " g:50 ")" => ltSet f g

notation "≤(" f:50 ", " g:50 ")" => leSet f g

notation "=(" f:50 ", " g:50 ")" => eqSet f g

notation "≠(" f:50 ", " g:50 ")" => neSet f g

theorem mem_leSet {L A : Type*} [LinearOrder L] {f g : A → L} {a : A} :
    a ∈ ≤(f, g) ↔ f a ≤ g a := Iff.rfl

theorem not_mem_leSet {L A : Type*} [LinearOrder L] {f g : A → L} {a : A} :
    a ∉ ≤(f, g) ↔ g a < f a := by
  simp only [leSet, mem_setOf_eq, not_le]

def lt_SIdeal {L A : Type*} [LinearOrder L] (I : SIdeal A) (f g : A → L) : Prop :=
  ≤(g, f) ∈ I

def le_SIdeal {L A : Type*} [LinearOrder L] (I : SIdeal A) (f g : A → L) : Prop :=
  <(g, f) ∈ I

def eq_SIdeal {L A : Type*} [LinearOrder L] (I : SIdeal A) (f g : A → L) : Prop :=
  ≠(f, g) ∈ I

end Order

namespace SIdeal

notation f:50 " <"I:max g:50 => lt_SIdeal I f g

notation f:50 " ≤"I:max g:50 => le_SIdeal I f g

notation f:50 " ="I:max g:50 => eq_SIdeal I f g

instance {L A : Type*} [LinearOrder L] {I : SIdeal A} : IsPreorder (A → L) (le_SIdeal I) := sorry

instance {L A : Type*} [LinearOrder L] {I : SIdeal A} : IsTrans (A → L) (lt_SIdeal I) := sorry

private theorem eq_refl {L A : Type*} [LinearOrder L] {I : SIdeal A} (f : A → L) : f =I f := by
  unfold eq_SIdeal neSet
  simp
  apply Ideal.bot_mem

private theorem lt_trans {L A : Type*} [LinearOrder L] {I : SIdeal A} {f g h : A → L}
    (hfg : f <I g) (hgh : g <I h) : f <I h :=
  Trans.trans hfg hgh

end SIdeal

def Set.UpperBound {α : Type*} (le : α → α → Prop) (A : Set α) (a : α) : Prop :=
  ∀ x ∈ A, le x a

def Set.LeastUpperBound {α : Type*} (le : α → α → Prop) (A : Set α) (a : α) : Prop :=
  UpperBound le A a ∧ (∀ x, UpperBound le A x → le a x)

def Set.ExactUpperBound {α : Type*} (le lt : α → α → Prop) (A : Set α) (a : α) : Prop :=
  LeastUpperBound le A a ∧ (∀ p, lt p a → ∃ x ∈ A, le p x)


def Set.UpperBound_SIdeal {A L : Type*} [LinearOrder L] (I : SIdeal A) (S : Set (A → L))
    (h : A → L) : Prop :=
  UpperBound (· ≤I ·) S h

def Set.LeastUpperBound_SIdeal {A L : Type*} [LinearOrder L] (I : SIdeal A) (S : Set (A → L))
    (h : A → L) : Prop :=
  LeastUpperBound (· ≤I ·) S h

def Set.ExactUpperBound_SIdeal {A L : Type*} [LinearOrder L] (I : SIdeal A) (S : Set (A → L))
    (h : A → L) : Prop :=
  ExactUpperBound (· ≤I ·) (· <I ·) S h

def Order.FunsBelow {L A : Type*} [LinearOrder L] (h : A → L) : Set (A → L) :=
  {f : A → L | ∀ a, f a < h a}

/- An order has `true cofinality` if it has a linearly ordered cofinal subset. -/
def Order.hasTCF {α : Type*} (r : α → α → Prop) : Prop :=
  ∃ A : Set α, (∀ a ∈ A, ∀ b ∈ A, r a b ∨ r b a) ∧ (∀ x : α, ∃ y ∈ A, r x y)

def Ordinal.Prod (A : Set Ordinal) : Set (A → Ordinal) :=
  @Order.FunsBelow Ordinal A _ Subtype.val

instance {A : Set Ordinal} : FunLike (Ordinal.Prod A) A Ordinal where
  coe := fun f ↦ f.1
  coe_injective' := by
    aesop

def Order.SIdeal_cof {L A : Type*} [LinearOrder L] (S : Set (A → L)) (I : SIdeal A) :=
  @Order.cof S (fun f g ↦ f.1 ≤I g.1)

/- The cofinality an ideal `I` on a set of ordinals `A` induces on ∏ A. -/
def Ordinal.SIdeal_cof_Prod (A : Set Ordinal) (I : SIdeal A) :=
  Order.SIdeal_cof (Ordinal.Prod A) I

/- `C` is cofinal in `B` -/
def Order.IsCofinal_SIdeal {L A : Type*} [LinearOrder L] (B : Set (A → L)) (C : Set B)
    (I : SIdeal A) : Prop :=
  @IsCofinal B ⟨fun f g ↦ f.1 ≤I g.1⟩ C

example {L A : Type*} [LinearOrder L] (B : Set (A → L)) (C : Set B) (I : SIdeal A)
    (h : IsCofinal_SIdeal B C I) (g : B) : ∃ f ∈ C, g.1 ≤I f.1 := by
  exact h g

/- The `pcf` (Possible Cofinalities) of a set of ordinals `A` is the set of true cofinalities
that `∏ A` attains with any proper ideal on `A`. -/
def Ordinal.pcf (A : Set Ordinal) : Set Cardinal :=
  {SIdeal_cof_Prod A I | (I : SIdeal A) (_hI : Set.univ ∉ I) (_hTCF : @hasTCF (Prod A) (· ≤I ·))}


-- alt cofinality
/-
def Order.cof' (α : Type*) [Preorder α] : Cardinal :=
  ⨅ s : { s : Set α // IsCofinal s }, #s.1

def instPreorderSIdeal {A L : Type*} [LinearOrder L] (I : SIdeal A) : Preorder (A → L) where
    le := (· ≤I ·)
    le_refl := by
      intro f
      dsimp [LE.le, le_SIdeal, ltSet]
      simp_all only [lt_self_iff_false, setOf_false, I.empty_mem]
    le_trans := sorry
    lt_iff_le_not_le := sorry

def Order.SIdeal_cof' {L A : Type*} [LinearOrder L] (S : Set (A → L)) (I : SIdeal A) : Cardinal :=
  @cof' S (@Subtype.preorder (A → L) (instPreorderSIdeal I) S)
-/

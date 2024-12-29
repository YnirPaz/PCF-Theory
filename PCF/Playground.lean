import Mathlib

/- Current attempts at defining the basic objects of study. Everything very subject to change. -/

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

private theorem le_trans {L A : Type*} [Li : LinearOrder L] {I : SIdeal A} {f g h : A → L}
    (hfg : f <I g) (hgh : g <I h) : f <I h :=
  Trans.trans hfg hgh

end SIdeal

def Set.UpperBound {α : Type*} (le : α → α → Prop) (A : Set α) (a : α) : Prop :=
  ∀ x ∈ A, le x a

def Set.LeastUpperBound {α : Type*} (le : α → α → Prop) (A : Set α) (a : α) : Prop :=
  UpperBound le A a ∧ (∀ x, UpperBound le A x → le a x)

def Set.ExactUpperBound {α : Type*} (le lt : α → α → Prop) (A : Set α) (a : α) : Prop :=
  LeastUpperBound le A a ∧ (∀ p, lt p a → ∃ x ∈ A, le p x)


def Ordinal.UpperBound_SIdeal {A : Type*} (I : SIdeal A) (S : Set (A → Ordinal))
    (h : A → Ordinal) : Prop :=
  UpperBound (· ≤I ·) S h

def Ordinal.LeastUpperBound_SIdeal {A : Type*} (I : SIdeal A) (S : Set (A → Ordinal))
    (h : A → Ordinal) : Prop :=
  LeastUpperBound (· ≤I ·) S h

def Ordinal.ExactUpperBound_SIdeal {A : Type*} (I : SIdeal A) (S : Set (A → Ordinal))
    (h : A → Ordinal) : Prop :=
  ExactUpperBound (· ≤I ·) (· <I ·) S h

structure Order.FunsBelow {L A : Type*} [LinearOrder L] (h : A → L) where
  toFun : A → L
  lt : ∀ a, toFun a < h a
-- SetLike and FunLike for ↑


def Ordinal.Prod (A : Set Ordinal) := @Order.FunsBelow Ordinal A _ Subtype.val

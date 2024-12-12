import Mathlib

open Ordinal Cardinal Set Order

universe u v

namespace Ordinal

instance : Nonempty (Iio omega0.{u}) := ⟨0, omega0_pos⟩

theorem mk_Iio_subtype {o : Ordinal} {p : Iio o} : #(Iio p) = #(Iio p.1) := by
  apply mk_congr
  let f : Iio p → Iio p.1 := fun ⟨x, h⟩ ↦ ⟨x, h⟩
  let g : Iio p.1 → Iio p := fun ⟨x, h⟩ ↦ ⟨⟨x,
    have : p.1 < o := p.2
    have := h.trans this
    this⟩, h⟩
  exact ⟨f, g, congrFun rfl, congrFun rfl⟩

theorem two_lt_aleph0 : 2 < ℵ₀ := nat_lt_aleph0 2

theorem succ_pred_of_finite {o : Ordinal} (h : 0 < o) (h' : o < ω) : succ o.pred = o := by
  have := @boundedLimitRecOn ω isLimit_omega0
    (fun n ↦ if 0 < n.1 then succ n.1.pred = n else True) ⟨o, h'⟩
    (by simp)
    (by simp)
    (fun o h ↦ False.elim ((omega0_le_of_isLimit h).not_lt o.2))
  simp only [if_true_right, h, true_implies] at this
  exact this

theorem type_Iio (α : Ordinal.{u}) : type (· < · : Iio α → Iio α → Prop) = lift.{u + 1} α := by
  have inst : IsWellOrder _ (· < · : α.toType → α.toType → Prop) := isWellOrder_lt
  have := (enumIsoToType α).toRelIsoLT.ordinal_lift_type_eq
  rw [lift_id'.{u, u + 1}] at this
  rw [this]
  congr
  exact type_toType α

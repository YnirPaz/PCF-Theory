import Mathlib

namespace Ordinal

protected theorem pos_of_gt {a b : Ordinal} (h : a < b) : 0 < b :=
  lt_of_le_of_lt (Ordinal.zero_le a) h

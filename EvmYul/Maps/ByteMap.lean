module

public import Std.Data.TreeMap

public import EvmYul.Wheels

/-!
# Byte maps

`ByteMap` (`UInt256 → UInt8`) is a `Std.TreeMap` ordered by `compare`.

`Std.TreeMap` is maintained in Lean core and is what Batteries recommends instead of
`Batteries.RBMap`. Its lemma library (`Std.TreeMap.getElem?_insert`, `Std.TreeMap.contains_erase`,
...) only assumes a lawful comparator (`Std.TransOrd`, `Std.LawfulEqOrd`); those instances for
`UInt256` and `AccountAddress` are proved next to the types. Iteration (`foldl`, `toList`,
`toArray`) visits keys in increasing order, exactly as the former `Batteries.RBMap` did, so the trie
roots computed from these maps do not change. See `EvmYul.Maps.TreeMapTests`.
-/

public section

namespace EvmYul

section RemoveLater

abbrev ByteMap := Std.TreeMap UInt256 UInt8 compare

end RemoveLater

end EvmYul

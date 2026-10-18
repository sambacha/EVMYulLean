# `EvmYul/Maps/`: Finite maps

The map types of the state (byte, storage and tree maps), their reasoning principles, and trie roots.

## Files

The library children of this folder (layout check L13 keeps this list complete):

- `ByteMap.lean`: Byte maps.
- `StorageMap.lean`: Account storage.
- `TreeMap.lean`: Reasoning principles for the tree maps.
- `TrieRoot.lean`: Trie roots through the Python helper.
- `TrieRootModel.lean`: The trie-root temporary file is always cleaned up (formal proof over a file-system model).

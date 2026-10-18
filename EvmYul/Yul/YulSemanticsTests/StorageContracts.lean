module

public import EvmYul.Yul.Interpreter
public import EvmYul.Yul.YulNotation

@[expose] public section

/-!
# The `Storage` and `Storage2` contracts of the Yul semantics test

Yul code (compiled from `Storage.sol` / `Storage2.sol`, see `Storage.yul` / `Storage2.yul`) used by
the world state `stateEg₁` of `EvmYul/Yul/YulSemanticsTests/Main.lean`. Split from that file
(Rule 4); the code is unchanged.
-/

namespace EvmYul

namespace Yul

open Ast SizeLemmas

/-- The Yul code of the `Storage` contract of the fixture (see `README.md`). -/
def storageCode : YulContract :=
{
dispatcher := 
      <s {
                mstore(64, 0x80)
                if iszero(lt(calldatasize(), 4))
                {
                    switch shr(224, calldataload(0))
                    case 0x2e64cec1 { external_fun_retrieve() }
                    case 0x6057361d { external_fun_store() }
                    case 0xd54d0506 {
                        external_fun_storageCallCodeTest()
                    }
                    case 0xdd15ce8e {
                        external_fun_storageDelegateCallTest()
                    }
                }
                revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            } >,
functions := (∅ : Finmap (fun (_ : YulFunctionName) ↦ Yul.Ast.FunctionDefinition))

            |>.insert
          "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb"
          <f
          function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            { revert(0, 0) }
            
           >

          |>.insert
          "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b"
          <f
          function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
            { revert(0, 0) }
            
           >

          |>.insert
          "abi_decode"
          <f
          function abi_decode(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            
           >

          |>.insert
          "abi_encode_uint256_to_uint256"
          <f
          function abi_encode_uint256_to_uint256(value, pos)
            { mstore(pos, value) }
            
           >

          |>.insert
          "abi_encode_uint256"
          <f
          function abi_encode_uint256(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                abi_encode_uint256_to_uint256(value0, headStart)
            }
            
           >

          |>.insert
          "external_fun_retrieve"
          <f
          function external_fun_retrieve()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                let ret := fun_retrieve()
                let memPos := mload(64)
                let _1 := abi_encode_uint256(memPos, ret)
                return(memPos, sub(_1, memPos))
            }
            
           >

          |>.insert
          "validator_revert_uint256"
          <f
          function validator_revert_uint256(value)
            { if 0 { revert(0, 0) } }
            
           >

          |>.insert
          "abi_decode_uint256"
          <f
          function abi_decode_uint256(offset, end) -> value
            {
                value := calldataload(offset)
                validator_revert_uint256(value)
            }
            
           >

          |>.insert
          "abi_decode_tuple_uint256"
          <f
          function abi_decode_tuple_uint256(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_uint256(headStart, dataEnd)
            }
            
           >

          |>.insert
          "external_fun_store"
          <f
          function external_fun_store()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _1 := abi_decode_tuple_uint256(4, calldatasize())
                fun_store(_1)
                return(0, 0)
            }
            
           >

          |>.insert
          "external_fun_storageCallCodeTest"
          <f
          function external_fun_storageCallCodeTest()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                fun_storageCallCodeTest()
                return(0, 0)
            }
            
           >

          |>.insert
          "external_fun_storageDelegateCallTest"
          <f
          function external_fun_storageDelegateCallTest()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                fun_storageDelegateCallTest()
                return(0, 0)
            }
            
           >

          |>.insert
          "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74"
          <f
          function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
            
           >

          |>.insert
          "fun_retrieve"
          <f
          function fun_retrieve() -> var
            {
                var :=  sload( 0x00)
            }
            
           >

          |>.insert
          "update_byte_slice_shift"
          <f
          function update_byte_slice_shift(value, toInsert) -> result
            {
                toInsert := toInsert
                result := toInsert
            }
            
           >

          |>.insert
          "update_storage_value_offset_uint256_to_uint256"
          <f
          function update_storage_value_offset_uint256_to_uint256(slot, value)
            {
                let _1 := sload(slot)
                let _2 := update_byte_slice_shift(_1, value)
                sstore(slot, _2)
            }
            
           >

          |>.insert
          "fun_store"
          <f
          function fun_store(var_num)
            {
                update_storage_value_offset_uint256_to_uint256(0x00, var_num)
            }
            
           >

          |>.insert
          "panic_error_0x41"
          <f
          function panic_error_0x41()
            {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x41)
                revert(0, 0x24)
            }
            
           >

          |>.insert
          "finalize_allocation"
          <f
          function finalize_allocation(memPtr, size)
            {
                let newFreePtr := add(memPtr, and(add(size, 31), not(31)))
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { panic_error_0x41() }
                mstore(64, newFreePtr)
            }
            
           >

          |>.insert
          "allocate_memory"
          <f
          function allocate_memory(size) -> memPtr
            {
                memPtr := mload(64)
                finalize_allocation(memPtr, size)
            }
            
           >

          |>.insert
          "array_allocation_size_bytes"
          <f
          function array_allocation_size_bytes(length) -> size
            {
                if gt(length, 0xffffffffffffffff) { panic_error_0x41() }
                size := and(add(length, 31), not(31))
                size := add(size, 0x20)
            }
            
           >

          |>.insert
          "allocate_memory_array_bytes"
          <f
          function allocate_memory_array_bytes(length) -> memPtr
            {
                let _1 := array_allocation_size_bytes(length)
                memPtr := allocate_memory(_1)
                mstore(memPtr, length)
            }
            
           >

          |>.insert
          "extract_returndata"
          <f
          function extract_returndata() -> data
            {
                let _1 := returndatasize()
                switch _1
                case 0 { data := 96 }
                default {
                    let _2 := returndatasize()
                    data := allocate_memory_array_bytes(_2)
                    let _3 := returndatasize()
                    returndatacopy(add(data, 0x20), 0, _3)
                }
            }
            
           >

          |>.insert
          "fun_storageCallCodeTest"
          <f
          function fun_storageCallCodeTest()
            {
                let expr_mpos :=  mload(64)
                let _1 := add(expr_mpos, 0x20)
                mstore(_1, shl(224, 0x2a24ab1f))
                _1 := add(expr_mpos, 36)
                mstore(expr_mpos, add(sub(_1, expr_mpos),  not(31)))
                finalize_allocation(expr_mpos, sub(_1, expr_mpos))
                let _2 := mload(expr_mpos)
                let _3 := gas()
                pop(callcode(_3,  4, 0, add(expr_mpos,  0x20),  _2, 0, 0))
                pop(extract_returndata())
            }
            
           >

          |>.insert
          "fun_storageDelegateCallTest"
          <f
          function fun_storageDelegateCallTest()
            {
                let expr_55_mpos :=  mload(64)
                let _1 := add(expr_55_mpos, 0x20)
                mstore(_1,  shl(224, 0x2a24ab1f))
                _1 := add(expr_55_mpos, 36)
                mstore(expr_55_mpos, add(sub(_1, expr_55_mpos),  not(31)))
                finalize_allocation(expr_55_mpos, sub(_1, expr_55_mpos))
                let _2 := mload(expr_55_mpos)
                let _3 := gas()
                pop(delegatecall(_3,  4,  add(expr_55_mpos,  0x20),  _2, 0, 0))
                pop(extract_returndata())
            }
        
           >


}  

/-- The Yul code of the `Storage2` contract of the fixture (see `README.md`). -/
def storage2Code : YulContract :=
 {
dispatcher := 
      <s {
                mstore(64, 0x80)
                if iszero(lt(calldatasize(), 4))
                {
                    if eq(0x2a24ab1f, shr(224, calldataload(0))) { external_fun_store5() }
                }
                revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            } >,
functions := (∅ : Finmap (fun (_ : YulFunctionName) ↦ Yul.Ast.FunctionDefinition))

            |>.insert
          "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb"
          <f
          function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            { revert(0, 0) }
            
           >

          |>.insert
          "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b"
          <f
          function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
            { revert(0, 0) }
            
           >

          |>.insert
          "abi_decode"
          <f
          function abi_decode(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            
           >

          |>.insert
          "external_fun_store5"
          <f
          function external_fun_store5()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                fun_store5()
                return(0, 0)
            }
            
           >

          |>.insert
          "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74"
          <f
          function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
            
           >

          |>.insert
          "update_byte_slice_shift"
          <f
          function update_byte_slice_shift(value, toInsert) -> result
            {
                toInsert := toInsert
                result := toInsert
            }
            
           >

          |>.insert
          "update_storage_value_offset_uint256_to_uint256"
          <f
          function update_storage_value_offset_uint256_to_uint256(slot, value)
            {
                let _1 := sload(slot)
                let _2 := update_byte_slice_shift(_1, value)
                sstore(slot, _2)
            }
            
           >

          |>.insert
          "fun_store5"
          <f
          function fun_store5()
            {
                update_storage_value_offset_uint256_to_uint256(0x00,  0x05)
            }
        
           >


}

end Yul

end EvmYul

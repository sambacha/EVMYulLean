module

public import EvmYul.Yul.Interpreter
public import EvmYul.Yul.YulNotation

@[expose] public section

/-!
# The `Caller` and `Caller2` contracts of the Yul semantics test

Yul code (compiled from `Caller.sol` / `Caller2.sol`, see `Caller.yul` / `Caller2.yul`) used by the
world state `stateEg₁` of `EvmYul/Yul/YulSemanticsTests/Main.lean`. Split from that file (Rule 4);
the code is unchanged.
-/

namespace EvmYul

namespace Yul

open Ast SizeLemmas

/-- The Yul code of the `Caller` contract of the fixture (see `README.md`). -/
def callerCode : YulContract :=
  {
dispatcher := 
      <s {
                mstore(64, 0x80)
                if iszero(lt(calldatasize(), 4))
                {
                    if eq(0x5ec1cee6, shr(224, calldataload(0)))
                    {
                        external_fun_testStoreAndRetrieveExternal()
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
          "external_fun_testStoreAndRetrieveExternal"
          <f
          function external_fun_testStoreAndRetrieveExternal()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _1 := abi_decode_tuple_uint256(4, calldatasize())
                fun_testStoreAndRetrieveExternal(_1)
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
          "revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20"
          <f
          function revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20()
            { revert(0, 0) }
            
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
          "abi_decode_fromMemory"
          <f
          function abi_decode_fromMemory(headStart, dataEnd)
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
          "revert_forward"
          <f
          function revert_forward()
            {
                let pos := mload(64)
                let _1 := returndatasize()
                returndatacopy(pos, 0, _1)
                let _2 := returndatasize()
                revert(pos, _2)
            }
            
           >

          |>.insert
          "abi_decode_t_uint256_fromMemory"
          <f
          function abi_decode_t_uint256_fromMemory(offset, end) -> value
            {
                value := mload(offset)
                validator_revert_uint256(value)
            }
            
           >

          |>.insert
          "abi_decode_uint256_fromMemory"
          <f
          function abi_decode_uint256_fromMemory(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_t_uint256_fromMemory(headStart, dataEnd)
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
          "fun_testStoreAndRetrieveExternal"
          <f
          function fun_testStoreAndRetrieveExternal(var_v)
            {
                let _1 := 1
                if iszero(_1)
                {
                    revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20()
                }
                let _2 :=  mload(64)
                mstore(_2,  shl(224, 0x6057361d))
                let _3 := abi_encode_uint256(add(_2, 4), var_v)
                let _4 := gas()
                let _5 := call(_4,  2,  0, _2, sub(_3, _2), _2, 0)
                if iszero(_5) { revert_forward() }
                if _5
                {
                    let _6 := 0
                    if 0 { _6 := returndatasize() }
                    finalize_allocation(_2, _6)
                    abi_decode_fromMemory(_2, add(_2, _6))
                }
                let _7 :=  mload(64)
                mstore(_7,  shl(224, 0x2e64cec1))
                let _8 := add(_7,  4)
                let _9 := gas()
                let _10 := call(_9,  2,  0,  _7, sub( _8,  _7), _7, 32)
                if iszero(_10) { revert_forward() }
                let expr
                if _10
                {
                    let _11 := 32
                    let _12 := returndatasize()
                    if gt(32, _12) { _11 := returndatasize() }
                    finalize_allocation(_7, _11)
                    expr := abi_decode_uint256_fromMemory(_7, add(_7, _11))
                }
                update_storage_value_offset_uint256_to_uint256( 0,  expr)
            }
        
           >


}

/-- The Yul code of the `Caller2` contract of the fixture (see `README.md`). -/
def caller2Code : YulContract :=
  {
dispatcher := 
      <s {
                mstore(64, 0x80)
                if iszero(lt(calldatasize(), 4))
                {
                    switch shr(224, calldataload(0))
                    case 0x37cbaee8 {
                        external_fun_testStaticStore()
                    }
                    case 0x5ec1cee6 {
                        external_fun_testStoreAndRetrieveExternal()
                    }
                    case 0x8b1218f9 {
                        external_fun_testStaticRetrieve()
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
          "external_fun_testStaticStore"
          <f
          function external_fun_testStaticStore()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _1 := abi_decode_tuple_uint256(4, calldatasize())
                let ret := fun_testStaticStore(_1)
                let memPos := mload(64)
                let _2 := abi_encode_uint256(memPos, ret)
                return(memPos, sub(_2, memPos))
            }
            
           >

          |>.insert
          "external_fun_testStoreAndRetrieveExternal"
          <f
          function external_fun_testStoreAndRetrieveExternal()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _1 := abi_decode_tuple_uint256(4, calldatasize())
                fun_testStoreAndRetrieveExternal(_1)
                return(0, 0)
            }
            
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
          "external_fun_testStaticRetrieve"
          <f
          function external_fun_testStaticRetrieve()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                let ret := fun_testStaticRetrieve()
                let memPos := mload(64)
                let _1 := abi_encode_uint256(memPos, ret)
                return(memPos, sub(_1, memPos))
            }
            
           >

          |>.insert
          "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74"
          <f
          function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
            
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
          "abi_decode_t_uint256_fromMemory"
          <f
          function abi_decode_t_uint256_fromMemory(offset, end) -> value
            {
                value := mload(offset)
                validator_revert_uint256(value)
            }
            
           >

          |>.insert
          "abi_decode_uint256_fromMemory"
          <f
          function abi_decode_uint256_fromMemory(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_t_uint256_fromMemory(headStart, dataEnd)
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
          "fun_testStaticStore"
          <f
          function fun_testStaticStore(var_value) -> var
            {
                var :=  0
                let expr_105_mpos :=  mload(64)
                let _1 := 0x20
                let _2 := add(expr_105_mpos, _1)
                mstore(_2, shl(224, 0x6057361d))
                _2 := add(expr_105_mpos, 36)
                let _3 := abi_encode_uint256(_2, var_value)
                mstore(expr_105_mpos, add(sub(_3, expr_105_mpos),  not(31)))
                finalize_allocation(expr_105_mpos, sub(_3, expr_105_mpos))
                let _4 := mload(expr_105_mpos)
                let _5 := gas()
                pop(staticcall(_5,  2,  add(expr_105_mpos, _1), _4, 0, 0))
                let expr_106_component_2_mpos := extract_returndata()
                let _6 := mload( expr_106_component_2_mpos)
                let expr := abi_decode_uint256_fromMemory(add(expr_106_component_2_mpos, _1), add(add(expr_106_component_2_mpos,  _6),  _1))
                update_storage_value_offset_uint256_to_uint256( 0,  expr)
            }
            
           >

          |>.insert
          "revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20"
          <f
          function revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20()
            { revert(0, 0) }
            
           >

          |>.insert
          "abi_decode_fromMemory"
          <f
          function abi_decode_fromMemory(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            
           >

          |>.insert
          "revert_forward"
          <f
          function revert_forward()
            {
                let pos := mload(64)
                let _1 := returndatasize()
                returndatacopy(pos, 0, _1)
                let _2 := returndatasize()
                revert(pos, _2)
            }
            
           >

          |>.insert
          "fun_testStoreAndRetrieveExternal"
          <f
          function fun_testStoreAndRetrieveExternal(var_v)
            {
                let _1 := extcodesize( 2)
                if iszero(_1)
                {
                    revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20()
                }
                let _2 :=  mload(64)
                mstore(_2,  shl(224, 0x6057361d))
                let _3 := abi_encode_uint256(add(_2, 4), var_v)
                let _4 := gas()
                let _5 := call(_4,  2,  0, _2, sub(_3, _2), _2, 0)
                if iszero(_5) { revert_forward() }
                if _5
                {
                    let _6 := 0
                    if 0 { _6 := returndatasize() }
                    finalize_allocation(_2, _6)
                    abi_decode_fromMemory(_2, add(_2, _6))
                }
                let _7 :=  mload(64)
                mstore(_7,  shl(224, 0x2e64cec1))
                let _8 := add(_7,  4)
                let _9 := gas()
                let _10 := call(_9,  2,  0,  _7, sub( _8,  _7), _7, 32)
                if iszero(_10) { revert_forward() }
                let expr
                if _10
                {
                    let _11 := 32
                    let _12 := returndatasize()
                    if gt(32, _12) { _11 := returndatasize() }
                    finalize_allocation(_7, _11)
                    expr := abi_decode_uint256_fromMemory(_7, add(_7, _11))
                }
                update_storage_value_offset_uint256_to_uint256( 0,  expr)
            }
            
           >

          |>.insert
          "fun_testStaticRetrieve"
          <f
          function fun_testStaticRetrieve() -> var_
            {
                var_ :=  0
                let expr_mpos :=  mload(64)
                let _1 := 0x20
                let _2 := add(expr_mpos, _1)
                mstore(_2,  shl(224, 0x2e64cec1))
                _2 := add(expr_mpos, 36)
                mstore(expr_mpos, add(sub(_2, expr_mpos),  not(31)))
                finalize_allocation(expr_mpos, sub(_2, expr_mpos))
                let _3 := mload(expr_mpos)
                let _4 := gas()
                pop(staticcall(_4,  2,  add(expr_mpos, _1), _3, 0, 0))
                let expr_component_mpos := extract_returndata()
                let _5 := mload( expr_component_mpos)
                let expr := abi_decode_uint256_fromMemory(add(expr_component_mpos, _1), add(add(expr_component_mpos,  _5),  _1))
                update_storage_value_offset_uint256_to_uint256( 0,  expr)
            }
        
           >


}

end Yul

end EvmYul

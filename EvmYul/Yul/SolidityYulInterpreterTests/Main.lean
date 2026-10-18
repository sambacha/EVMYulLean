import EvmYul.Yul.Interpreter
import EvmYul.Yul.StateOps

import GeneratedEvmYul.access_large_memory_offsets.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.ambiguous_vars.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.and_create.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.and_create2.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.blobbasefee.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.blobhash.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.clz.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.create2.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.datacopy.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.dataoffset.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.datasize.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.difficulty.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.exp.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.external_call_to_self.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.external_call_unexecuted.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.external_callcode_unexecuted.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.external_delegatecall_unexecuted.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.external_staticcall_unexecuted.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.hex_literals.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.loop.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.long_object_name.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.mcopy.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.mcopy_memory_access_out_of_range.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.mcopy_memory_expansion_on_read.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.mcopy_memory_expansion_on_write.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.mcopy_memory_expansion_zero_size.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.mcopy_overlap.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.pop_byte_shr_call.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.prevrandao.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.self_balance.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.side_effect_free.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.simple_mstore.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.smoke.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.switch_statement.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.transient_storage.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.zero_length_reads.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.zero_length_reads_and_revert.SolidityYulInterpreterTest.main_gen
import GeneratedEvmYul.zero_range.SolidityYulInterpreterTest.main_gen

namespace EvmYul
namespace Yul
namespace SolidityYulInterpreterTests

def testAddress : AccountAddress :=
  AccountAddress.ofUInt256 ⟨0⟩

def testAccount : Account .Yul :=
  { code := Inhabited.default
    balance := ⟨1000⟩
    nonce := ⟨0⟩
    storage := ∅
    tstorage := ∅
  }

def initialSharedState : SharedState .Yul :=
  { (Inhabited.default : SharedState .Yul) with
    accountMap := (∅ : AccountMap .Yul).insert testAddress testAccount
    executionEnv :=
      { (Inhabited.default : ExecutionEnv .Yul) with
        codeOwner := testAddress
        source := testAddress
        sender := testAddress
        perm := true
      }
  }

def initialState : State :=
  State.Ok initialSharedState (Inhabited.default : VarStore)

def runMain (body : List Ast.Stmt) : Except Exception State :=
  exec 1024 (.Block body) none initialState

def machineState? : Except Exception State → Option MachineState
  | .ok (.Ok sharedState _) => some sharedState.toMachineState
  | _ => none

def memorySize? (result : Except Exception State) : Option Nat :=
  (machineState? result).map (fun machineState => machineState.memory.size)

def activeBytes? (result : Except Exception State) : Option Nat :=
  (machineState? result).map (fun machineState => machineState.activeWords.toNat * 32)

def memoryByte? (result : Except Exception State) (offset : Nat) : Option Nat :=
  (machineState? result).map (fun machineState => (machineState.memory.data.getD offset 0).toNat)

def storageValue? (result : Except Exception State) (slot : UInt256) : Option UInt256 :=
  match result with
  | .ok (.Ok sharedState _) =>
      match sharedState.accountMap.find? testAddress with
      | .some account => some (account.storage.getD slot ⟨0⟩)
      | .none => none
  | _ => none

def expectEq (name : String) (got expected : Option Nat) : IO Unit := do
  if got == expected then
    IO.println s!"PASS {name}"
  else
    throw <| IO.userError s!"FAIL {name}: got {got}, expected {expected}"

def expectUInt256Eq (name : String) (got expected : Option UInt256) : IO Unit := do
  if got == expected then
    IO.println s!"PASS {name}"
  else
    throw <| IO.userError s!"FAIL {name}: got {got.map repr}, expected {expected.map repr}"

def expectOk (name : String) (result : Except Exception State) : IO Unit := do
  match result with
  | .ok (.Ok _ _) => IO.println s!"PASS {name}"
  | .ok _ => throw <| IO.userError s!"FAIL {name}: got non-Ok state"
  | .error e => throw <| IO.userError s!"FAIL {name}: interpreter error {repr e}"

def expectNonOk (name : String) (result : Except Exception State) : IO Unit := do
  match result with
  | .ok (.Ok _ _) => throw <| IO.userError s!"FAIL {name}: got Ok state"
  | .ok _ => IO.println s!"PASS {name}"
  | .error e => throw <| IO.userError s!"FAIL {name}: interpreter error {repr e}"

def expectError (name expected : String) (result : Except Exception State) : IO Unit := do
  match result with
  | .error e =>
      let got := toString (repr e)
      if got == expected then
        IO.println s!"PASS {name}"
      else
        throw <| IO.userError s!"FAIL {name}: got interpreter error {got}, expected {expected}"
  | .ok _ => throw <| IO.userError s!"FAIL {name}: got state, expected error {expected}"

def expectInterpretsOk (name : String) (body : List Ast.Stmt) : IO Unit := do
  IO.eprintln s!"RUN {name}"
  expectOk s!"{name} exits normally" (runMain body)

def expectInterpretsNonOk (name : String) (body : List Ast.Stmt) : IO Unit := do
  IO.eprintln s!"RUN {name}"
  expectNonOk s!"{name} exits non-Ok" (runMain body)

def expectInterpretsError (name expected : String) (body : List Ast.Stmt) : IO Unit := do
  IO.eprintln s!"RUN {name}"
  expectError s!"{name} errors with {expected}" expected (runMain body)

def skipInterprets (name reason : String) : IO Unit := do
  IO.eprintln s!"RUN {name}"
  IO.println s!"SKIP {name}: {reason}"

def testSmoke : IO Unit := do
  let result := runMain GeneratedEvmYul.smoke.SolidityYulInterpreterTest.main.body
  expectOk "smoke exits normally" result
  expectEq "smoke memory size" (memorySize? result) (some 0)
  expectEq "smoke active memory bytes" (activeBytes? result) (some 0)

def testSimpleMstore : IO Unit := do
  let result := runMain GeneratedEvmYul.simple_mstore.SolidityYulInterpreterTest.main.body
  expectOk "simple_mstore exits normally" result
  expectEq "simple_mstore memory size" (memorySize? result) (some 42)
  expectEq "simple_mstore active memory bytes" (activeBytes? result) (some 64)
  expectEq "simple_mstore mstore value byte" (memoryByte? result 41) (some 11)

def testSwitchStatement : IO Unit := do
  let result := runMain GeneratedEvmYul.switch_statement.SolidityYulInterpreterTest.main.body
  expectOk "switch_statement exits normally" result
  expectEq "switch_statement memory size" (memorySize? result) (some 33)
  expectEq "switch_statement active memory bytes" (activeBytes? result) (some 64)
  expectEq "switch_statement selected case byte" (memoryByte? result 32) (some 2)

def testDatacopy : IO Unit := do
  let result := runMain GeneratedEvmYul.datacopy.SolidityYulInterpreterTest.main.body
  expectOk "datacopy exits normally" result
  expectUInt256Eq "datacopy storage slot 0"
    (storageValue? result ⟨0⟩)
    (some ⟨0x6465636f00000000000000000000000000000000000000000000000000000000⟩)
  expectUInt256Eq "datacopy storage slot 1"
    (storageValue? result ⟨1⟩)
    (some ⟨0x636f6465636f6465000000000000000000000000000000000000000000000000⟩)

def testDataoffset : IO Unit := do
  let result := runMain GeneratedEvmYul.dataoffset.SolidityYulInterpreterTest.main.body
  expectOk "dataoffset exits normally" result
  expectUInt256Eq "dataoffset storage slot 0" (storageValue? result ⟨0⟩) (some ⟨0x6e⟩)
  expectUInt256Eq "dataoffset storage slot 1" (storageValue? result ⟨1⟩) (some ⟨0x70c⟩)

def testDatasize : IO Unit := do
  let result := runMain GeneratedEvmYul.datasize.SolidityYulInterpreterTest.main.body
  expectOk "datasize exits normally" result
  expectUInt256Eq "datasize storage slot 0" (storageValue? result ⟨0⟩) (some ⟨0xb64⟩)
  expectUInt256Eq "datasize storage slot 1" (storageValue? result ⟨1⟩) (some ⟨0x109⟩)

def run : IO Unit := do
  skipInterprets "access_large_memory_offsets"
    "executing this fixture currently triggers unbounded memory allocation in the interpreter"
  expectInterpretsOk "ambiguous_vars"
    GeneratedEvmYul.ambiguous_vars.SolidityYulInterpreterTest.main.body
  skipInterprets "and_create"
    "executing this fixture currently reaches a static-mode path that can trigger a Lean panic"
  skipInterprets "and_create2"
    "executing this fixture currently reaches a missing-function path that can trigger a Lean panic"
  expectInterpretsOk "blobbasefee"
    GeneratedEvmYul.blobbasefee.SolidityYulInterpreterTest.main.body
  expectInterpretsOk "blobhash"
    GeneratedEvmYul.blobhash.SolidityYulInterpreterTest.main.body
  skipInterprets "clz"
    "executing this fixture currently reaches a missing-function path that can trigger a Lean panic"
  skipInterprets "create2"
    "executing this fixture currently reaches a missing-function path that can trigger a Lean panic"
  testDatacopy
  testDataoffset
  testDatasize
  skipInterprets "difficulty"
    "executing this fixture currently reaches a missing-function path that can trigger a Lean panic"
  expectInterpretsOk "exp"
    GeneratedEvmYul.exp.SolidityYulInterpreterTest.main.body
  expectInterpretsError "external_call_to_self" "YulHalt: (holds a state and a value)"
    GeneratedEvmYul.external_call_to_self.SolidityYulInterpreterTest.main.body
  expectInterpretsOk "external_call_unexecuted"
    GeneratedEvmYul.external_call_unexecuted.SolidityYulInterpreterTest.main.body
  expectInterpretsOk "external_callcode_unexecuted"
    GeneratedEvmYul.external_callcode_unexecuted.SolidityYulInterpreterTest.main.body
  expectInterpretsOk "external_delegatecall_unexecuted"
    GeneratedEvmYul.external_delegatecall_unexecuted.SolidityYulInterpreterTest.main.body
  expectInterpretsError "external_staticcall_unexecuted" "StaticModeViolation"
    GeneratedEvmYul.external_staticcall_unexecuted.SolidityYulInterpreterTest.main.body
  expectInterpretsOk "hex_literals"
    GeneratedEvmYul.hex_literals.SolidityYulInterpreterTest.main.body
  expectInterpretsOk "loop"
    GeneratedEvmYul.loop.SolidityYulInterpreterTest.main.body
  expectInterpretsOk "long_object_name"
    GeneratedEvmYul.long_object_name.SolidityYulInterpreterTest.main.body
  expectInterpretsOk "mcopy"
    GeneratedEvmYul.mcopy.SolidityYulInterpreterTest.main.body
  skipInterprets "mcopy_memory_access_out_of_range"
    "its `mstore8(0xffffffffffffffff, 1)` makes the interpreter allocate 2^64 bytes of memory \
      (the process is killed by SIGSEGV), like access_large_memory_offsets"
  expectInterpretsOk "mcopy_memory_expansion_on_read"
    GeneratedEvmYul.mcopy_memory_expansion_on_read.SolidityYulInterpreterTest.main.body
  expectInterpretsOk "mcopy_memory_expansion_on_write"
    GeneratedEvmYul.mcopy_memory_expansion_on_write.SolidityYulInterpreterTest.main.body
  expectInterpretsOk "mcopy_memory_expansion_zero_size"
    GeneratedEvmYul.mcopy_memory_expansion_zero_size.SolidityYulInterpreterTest.main.body
  expectInterpretsOk "mcopy_overlap"
    GeneratedEvmYul.mcopy_overlap.SolidityYulInterpreterTest.main.body
  expectInterpretsOk "pop_byte_shr_call"
    GeneratedEvmYul.pop_byte_shr_call.SolidityYulInterpreterTest.main.body
  skipInterprets "prevrandao"
    "executing this fixture currently reaches a missing-function path that can trigger a Lean panic"
  expectInterpretsOk "self_balance"
    GeneratedEvmYul.self_balance.SolidityYulInterpreterTest.main.body
  expectInterpretsError "side_effect_free" "YulEXTCODESIZENotImplemented"
    GeneratedEvmYul.side_effect_free.SolidityYulInterpreterTest.main.body
  testSmoke
  testSimpleMstore
  testSwitchStatement
  expectInterpretsOk "transient_storage"
    GeneratedEvmYul.transient_storage.SolidityYulInterpreterTest.main.body
  expectInterpretsError "zero_length_reads" "StaticModeViolation"
    GeneratedEvmYul.zero_length_reads.SolidityYulInterpreterTest.main.body
  expectInterpretsError "zero_length_reads_and_revert" "StaticModeViolation"
    GeneratedEvmYul.zero_length_reads_and_revert.SolidityYulInterpreterTest.main.body
  expectInterpretsOk "zero_range"
    GeneratedEvmYul.zero_range.SolidityYulInterpreterTest.main.body

end SolidityYulInterpreterTests
end Yul
end EvmYul

def main : IO Unit :=
  EvmYul.Yul.SolidityYulInterpreterTests.run

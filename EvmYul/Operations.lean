module

public import EvmYul.UInt256
public import EvmYul.MachineState

public import Mathlib.Data.Finmap

/-!
# The operations of the EVM and of Yul

`Operation τ` for both machines (`τ = .EVM` or `.Yul`): the instruction groups of the Yellow Paper
(arithmetic, comparison, Keccak, environment, block, stack/memory/flow, push, dup, swap, log,
system), shared by the two semantics.
-/

public section

namespace EvmYul


@[expose] section

inductive OperationType where
  | Yul
  | EVM
  deriving DecidableEq, Repr

end

namespace Operation

section Operation

@[expose] section

/--
  Stop and Arithmetic Operations
-/
inductive SAOp (τ : OperationType) : Type where
  /--
    Stop: halts program execution
    δ: 0 ; α : 0
  -/
  | protected STOP : SAOp τ
  /--
    ADD: adds two stack values.
    δ: 2 ; α : 1
  -/
  | protected ADD : SAOp τ
  /--
    MUL: multiplies two stack values.
    δ: 2 ; α : 1
  -/
  | protected MUL : SAOp τ
  /--
    SUB: subtracts two stack values.
    δ: 2 ; α : 1
  -/
  | protected SUB : SAOp τ
  /--
    DIV: divides two stack values.
    δ: 2 ; α: 1
  -/
  | protected DIV : SAOp τ
  /--
    SDIV: signed integer division
    δ: 2 ; α: 1
  -/
  | protected SDIV : SAOp τ
  /--
    MOD: Modulo remainder operation
    δ: 2 ; α: 1
  -/
  | protected MOD : SAOp τ
  /--
    SMOD: signed integer remainder
    δ: 2 ; α: 1
  -/
  | protected SMOD : SAOp τ
  /--
    ADDMOD: addition modulo operation
    δ: 3 ; α: 1
  -/
  | protected ADDMOD : SAOp τ
  /--
    MULMOD: multiplication modulo operation
    δ: 3 ; α: 1
  -/
  | protected MULMOD : SAOp τ
  /--
    EXP: Exponential operation
    δ:2 ; α: 1
  -/
  | protected EXP : SAOp τ
  /--
    SIGNEXTEND: Extend length of two's complement signed integer
    δ: 2 ; α: 1
  -/
  | protected SIGNEXTEND : SAOp τ
  deriving DecidableEq, Repr

end

@[expose] section

/--
  Comparison & Bitwise Logic Operations
-/
inductive CBLOp (τ : OperationType) : Type where
  /--
    LT: less than comparison
    δ: 2 ; α: 1
  -/
  | protected LT : CBLOp τ
  /--
    GT: greater than comparison
    δ: 2 ; α: 1
  -/
  | protected GT : CBLOp τ
  /--
    SLT: signed less-than comparison
    δ:2 ; α: 1
  -/
  | protected SLT : CBLOp τ
  /--
    SGT: signed greater-than comparison
    δ: 2 ; α: 1
  -/
  | protected SGT : CBLOp τ
  /--
    EQ: equality test
    δ:2 ; α : 1
  -/
  | protected EQ : CBLOp τ
  /--
    ISZERO: simple not operation
    δ: 1 ; α : 1
  -/
  | protected ISZERO : CBLOp τ
  /--
    AND: bitwise and
    δ:2 ; α: 1
  -/
  | protected AND : CBLOp τ
  /--
    OR: bitwise or
    δ: 2 ; α: 1
  -/
  | protected OR : CBLOp τ
  /--
    XOR: bitwise xor
    δ: 2 ; α: 1
  -/
  | protected XOR : CBLOp τ
  /--
    NOT: bitwise not
    δ:1 ; α: 1
  -/
  | protected NOT : CBLOp τ
  /--
    BYTE: retrieve single byte from a word
    δ:2 ; α:1
  -/
  | protected BYTE : CBLOp τ
  /--
    SHL: shift left operation
    δ:2 ; α: 1
  -/
  | protected SHL : CBLOp τ
  /--
    SHR: logical shift right operation
    δ:2 ; α:1
  -/
  | protected SHR : CBLOp τ
  /--
    SAR: arithmetical shift right operation
    δ:2 ; α:1
  -/
  | protected SAR : CBLOp τ
  deriving DecidableEq, Repr

end

@[expose] section

/--
  Keccak operation.
-/
inductive KOp : OperationType → Type where
  /--
    KECCAK256: compute KECCAK256 hash
    δ:2 ; α: 1
  -/
  | protected KECCAK256 {τ : OperationType} : KOp τ
  deriving DecidableEq, Repr

end

@[expose] section

/--
  Environment Information.
-/
inductive EOp : OperationType → Type where
  /--
    ADDRESS: get the address of current executing account
    δ:0 ; α: 1
  -/
  | protected ADDRESS {τ : OperationType} : EOp τ
  /--
    BALANCE: get the balance of an input account
    δ:1 ; α: 1
  -/
  | protected BALANCE {τ : OperationType} : EOp τ
  /--
    ORIGIN: get execution origination address
    δ:0 ; α: 1
  -/
  | protected ORIGIN {τ : OperationType} : EOp τ
  /--
    CALLER: returns the caller address
    δ: 0 ; α: 1
  -/
  | protected CALLER {τ : OperationType} : EOp τ
  /--
    CALLVALUE: get deposited value by the instruction / transaction
    responsible for this execution.
    δ: 0 ; α: 1
  -/
  | protected CALLVALUE {τ : OperationType} : EOp τ
  /--
    CALLDATALOAD: get input data of current environment
    δ: 1 ;  α: 1
  -/
  | protected CALLDATALOAD {τ : OperationType} : EOp τ
  /--
    CALLDATASIZE: get size of input data in current environment
    δ: 0 ; α: 1
  -/
  | protected CALLDATASIZE {τ : OperationType} : EOp τ
  /--
    CALLDATACOPY: copy input data from environment to memory
    δ: 3 ; α: 0
  -/
  | protected CALLDATACOPY {τ : OperationType} : EOp τ
  /--
    CODESIZE: get the size of code running in current environment
    δ:0 ; α: 1
  -/
  | protected GASPRICE {τ : OperationType} : EOp τ
  /--
    CODECOPY: Copy code running in current environment to memory
    δ: 3 ; α: 0
  -/
  | protected CODESIZE {τ : OperationType} : EOp τ
  /--
    GASPRICE: Gas price in current execution environment
    δ: 0 ; α: 1
  -/
  | protected CODECOPY {τ : OperationType} : EOp τ
  /--
    EXTCODESIZE: get the size of an account's code
    δ:1 ; α: 1
  -/
  | protected EXTCODESIZE {τ : OperationType} : EOp τ
  /--
    EXTCODECOPY: copy an account's code to memory
    δ: 4 ; α: 0
  -/
  | protected EXTCODECOPY {τ : OperationType} : EOp τ
  /--
    RETURNDATASIZE: get the size of output data from the previous call
                    from the current environment.
    δ: 0 ; α: 1
  -/
  | protected RETURNDATASIZE {τ : OperationType} : EOp τ
  /--
    RETURNDATACOPY: copy output data from previous call to memory
    δ: 3 ; α: 0
  -/
  | protected RETURNDATACOPY {τ : OperationType} : EOp τ
  /--
    EXTCODEHASH: get hash of an account's code
    δ: 1 ; α: 1
  -/
  | protected EXTCODEHASH {τ : OperationType} : EOp τ
  deriving DecidableEq, Repr

end

@[expose] section

/--
  Block Information.
-/
inductive BOp : OperationType → Type where
  /--
    BLOCKHASH: get the hash of one of the 256 most recent blocks
    δ:1 ; α: 1
  -/
  | protected BLOCKHASH {τ : OperationType} : BOp τ
  /--
    COINBASE: get current's block beneficiary address
    δ: 0 ; α: 1
  -/
  | protected COINBASE {τ : OperationType} : BOp τ
  /--
    TIMESTAMP: get current block's timestamp
    δ: 0 ; α: 1
  -/
  | protected TIMESTAMP {τ : OperationType} : BOp τ
  /--
    NUMBER: get current block's number
    δ: 0 ; α: 1
  -/
  | protected NUMBER {τ : OperationType} : BOp τ
  | protected PREVRANDAO {τ : OperationType} : BOp τ
  /--
    GASLIMIT: get the gas limit for the current block
    δ: 0 ; α: 1
  -/
  | protected GASLIMIT {τ : OperationType} : BOp τ
  /--
    CHAINID: returns the chainid, β
    δ: 0 ; α: 1
  -/
  | protected CHAINID {τ : OperationType} : BOp τ
  /--
    SELFBALANCE: get the balance of the current executing account
    δ: 0 ; α: 1
  -/
  | protected SELFBALANCE {τ : OperationType} : BOp τ
  | protected BASEFEE {τ : OperationType} : BOp τ
  | protected BLOBHASH {τ : OperationType} : BOp τ
  | protected BLOBBASEFEE {τ : OperationType} : BOp τ
  deriving DecidableEq, Repr

end

@[expose] section

/--
  Stack, Memory, Storage and Flow Operations
-/
inductive SMSFOp : OperationType → Type where
  /--
    POP: remove an item from the stack
    δ: 1 ; α: 0
  -/
  | protected POP {τ : OperationType} : SMSFOp τ
  /--
    MLOAD: load word from memory
    δ: 1 ; α: 1
  -/
  | protected MLOAD {τ : OperationType} : SMSFOp τ
  /--
    MSTORE: save word in memory
    δ: 2 ; α: 0
  -/
  | protected MSTORE {τ : OperationType} : SMSFOp τ
  /--
    SLOAD: load word from storage
    δ: 1 ; α: 1
  -/
  | protected SLOAD {τ : OperationType} : SMSFOp τ
  /--
    SSTORE: Save word to storage
    δ:2 ; α: 0
  -/
  | protected SSTORE {τ : OperationType} : SMSFOp τ
  /--
    MSTORE8: save byte in memory
    δ: 2 ; α: 0
  -/
  | protected MSTORE8 {τ : OperationType} : SMSFOp τ
  /--
    JUMP: modify program counter
    δ:1 ; α: 0
  -/
  | protected JUMP : SMSFOp .EVM
  /--
    JUMPI: conditionally modify program counter
    δ: 2 ; α: 0
  -/
  | protected JUMPI : SMSFOp .EVM
  /--
    PC: get program counter before increment
    δ: 0 ; α: 1
  -/
  | protected PC : SMSFOp .EVM
  /--
    MSIZE: get the size of active memory in bytes
    δ: 0 ; α: 1
  -/
  | protected MSIZE {τ : OperationType} : SMSFOp τ
  /--
    GAS: get the amount of available gas
    δ: 0 ; α: 1
  -/
  | protected GAS {τ : OperationType} : SMSFOp τ
  /--
    JUMPDEST: mark a valid destination for jumps
    δ: 0 ; α: 0
  -/
  | protected JUMPDEST : SMSFOp .EVM
  /--
    EIP-1153
    https://eips.ethereum.org/EIPS/eip-1153
    TLOAD: load word from transient memory
    δ: 1 ; α: 1
  -/
  | protected TLOAD {τ : OperationType} : SMSFOp τ
  /--
    EIP-1153
    https://eips.ethereum.org/EIPS/eip-1153
    TSTORE: Save word to transient memory
    δ: 2 ; α: 0
  -/
  | protected TSTORE {τ : OperationType} : SMSFOp τ
  /--
    EIPS-5656
    MCOPY: copy memory areas
    δ: 3 ; α: 0
  -/
  | protected MCOPY {τ : OperationType} : SMSFOp τ  deriving DecidableEq, Repr

end

@[expose] section

/--
  Push operations.

  PUSH0 : pushes `0` to stack.
    δ: 0 ; α: 1

  PUSHn : pushes n bytes to stack.
    δ: 0 ; α: 1
-/
inductive POp : Type where
  | protected PUSH0 : POp
  | protected PUSH1 : POp
  | protected PUSH2 : POp
  | protected PUSH3 : POp
  | protected PUSH4 : POp
  | protected PUSH5 : POp
  | protected PUSH6 : POp
  | protected PUSH7 : POp
  | protected PUSH8 : POp
  | protected PUSH9 : POp
  | protected PUSH10 : POp
  | protected PUSH11 : POp
  | protected PUSH12 : POp
  | protected PUSH13 : POp
  | protected PUSH14 : POp
  | protected PUSH15 : POp
  | protected PUSH16 : POp
  | protected PUSH17 : POp
  | protected PUSH18 : POp
  | protected PUSH19 : POp
  | protected PUSH20 : POp
  | protected PUSH21 : POp
  | protected PUSH22 : POp
  | protected PUSH23 : POp
  | protected PUSH24 : POp
  | protected PUSH25 : POp
  | protected PUSH26 : POp
  | protected PUSH27 : POp
  | protected PUSH28 : POp
  | protected PUSH29 : POp
  | protected PUSH30 : POp
  | protected PUSH31 : POp
  | protected PUSH32 : POp
  deriving DecidableEq, Repr

end

@[expose] section

/--
  Duplicate Operations.

  DUPn: duplicates the nth item on the stack.
    δ: n ; α: n + 1
-/
inductive DOp : Type where
  | protected DUP1
  | protected DUP2
  | protected DUP3
  | protected DUP4
  | protected DUP5
  | protected DUP6
  | protected DUP7
  | protected DUP8
  | protected DUP9
  | protected DUP10
  | protected DUP11
  | protected DUP12
  | protected DUP13
  | protected DUP14
  | protected DUP15
  | protected DUP16
  deriving DecidableEq, Repr

end

@[expose] section

/--
  Exchange Operations.

  SWAPn: swaps the 1st and nth element of the stack.
    δ: n + 1 ; α: n + 1

-/
inductive ExOp : Type where
  | protected SWAP1  : ExOp
  | protected SWAP2  : ExOp
  | protected SWAP3  : ExOp
  | protected SWAP4  : ExOp
  | protected SWAP5  : ExOp
  | protected SWAP6  : ExOp
  | protected SWAP7  : ExOp
  | protected SWAP8  : ExOp
  | protected SWAP9  : ExOp
  | protected SWAP10 : ExOp
  | protected SWAP11 : ExOp
  | protected SWAP12 : ExOp
  | protected SWAP13 : ExOp
  | protected SWAP14 : ExOp
  | protected SWAP15 : ExOp
  | protected SWAP16 : ExOp
  deriving DecidableEq, Repr

end

@[expose] section

/--
  Logging Operations.

  LOGn: append log record with n topics.
    δ: n + 2 ; α : 0
-/
inductive LOp : OperationType → Type where
  | protected LOG0 {τ : OperationType} : LOp τ
  | protected LOG1 {τ : OperationType} : LOp τ
  | protected LOG2 {τ : OperationType} : LOp τ
  | protected LOG3 {τ : OperationType} : LOp τ
  | protected LOG4 {τ : OperationType} : LOp τ
  deriving DecidableEq, Repr

end

@[expose] section

/--
  System Operations.
-/
inductive SOp : OperationType → Type where
  /--
    CREATE: create a new account with associated code
    δ: 3 ; α: 1
  -/
  | protected CREATE {τ : OperationType} : SOp τ
  /--
    CALL: message call into an account
    δ: 7 ; α: 1
  -/
  | protected CALL {τ : OperationType} : SOp τ
  /--
    CALLCODE: message call into this account with an alternative account's code
    δ: 7 ; α: 1
  -/
  | protected CALLCODE {τ : OperationType} : SOp τ
  /--
    RETURN: Halt execution returning output data
    δ: 2 ; α: 0
  -/
  | protected RETURN {τ : OperationType} : SOp τ
  /--
    DELEGATECALL: message call into this account with an alternative account's code
                  but persisting the current values for sender and value
    δ: 6 ; α: 1
  -/
  | protected DELEGATECALL {τ : OperationType} : SOp τ
  /--
    CREATE2: create a new account with associated code
    δ: 4 ; α: 1
  -/
  | protected CREATE2 {τ : OperationType} : SOp τ
  /--
    STATICCALL: static message call into an account
    δ: 6 ; α: 1
  -/
  | protected STATICCALL {τ : OperationType} : SOp τ
  /--
    REVERT: halt execution reverting state changes but returning data and remaining gas
    δ: 2 ; α: 0
  -/
  | protected REVERT {τ : OperationType} : SOp τ
  /--
    INVALID: invalid opcode
    δ: ∅ ; α: ∅
  -/
  | protected INVALID {τ : OperationType} : SOp τ
  /--
    SELFDESTRUCT: halt and send entire balance to target.
    Deprecated; see EIP-6780
    δ: 1 ; α: 0
  -/
  | protected SELFDESTRUCT {τ : OperationType} : SOp τ
  deriving DecidableEq, Repr

end

end Operation

end Operation

open Operation

@[expose] section

inductive Operation : OperationType → Type where
  | protected StopArith    : {τ : OperationType} → SAOp   τ → Operation τ
  | protected CompBit      : {τ : OperationType} → CBLOp  τ → Operation τ
  | protected Keccak       : {τ : OperationType} → KOp    τ → Operation τ
  | protected Env          : {τ : OperationType} → EOp    τ → Operation τ
  | protected Block        : {τ : OperationType} → BOp    τ → Operation τ
  | protected StackMemFlow : {τ : OperationType} → SMSFOp τ → Operation τ
  | protected Push         : POp      → Operation .EVM
  | protected Dup          : DOp      → Operation .EVM
  | protected Exchange     : ExOp     → Operation .EVM
  | protected Log          : {τ : OperationType} → LOp    τ → Operation τ
  | protected System       : {τ : OperationType} → SOp    τ → Operation τ
  deriving DecidableEq, Repr

end
namespace Operation

@[expose, match_pattern]
abbrev STOP       {τ : OperationType} : Operation τ := .StopArith .STOP
@[expose] abbrev ADD        {τ : OperationType} : Operation τ := .StopArith .ADD
@[expose] abbrev MUL        {τ : OperationType} : Operation τ := .StopArith .MUL
@[expose] abbrev SUB        {τ : OperationType} : Operation τ := .StopArith .SUB
@[expose] abbrev DIV        {τ : OperationType} : Operation τ := .StopArith .DIV
@[expose] abbrev SDIV       {τ : OperationType} : Operation τ := .StopArith .SDIV
@[expose] abbrev MOD        {τ : OperationType} : Operation τ := .StopArith .MOD
@[expose] abbrev SMOD       {τ : OperationType} : Operation τ := .StopArith .SMOD
@[expose] abbrev ADDMOD     {τ : OperationType} : Operation τ := .StopArith .ADDMOD
@[expose] abbrev MULMOD     {τ : OperationType} : Operation τ := .StopArith .MULMOD
@[expose] abbrev EXP        {τ : OperationType} : Operation τ := .StopArith .EXP
@[expose] abbrev SIGNEXTEND {τ : OperationType} : Operation τ := .StopArith .SIGNEXTEND

@[expose] abbrev LT     {τ : OperationType} : Operation τ := .CompBit .LT
@[expose] abbrev GT     {τ : OperationType} : Operation τ := .CompBit .GT
@[expose] abbrev SLT    {τ : OperationType} : Operation τ := .CompBit .SLT
@[expose] abbrev SGT    {τ : OperationType} : Operation τ := .CompBit .SGT
@[expose] abbrev EQ     {τ : OperationType} : Operation τ := .CompBit .EQ
@[expose] abbrev ISZERO {τ : OperationType} : Operation τ := .CompBit .ISZERO
@[expose] abbrev AND    {τ : OperationType} : Operation τ := .CompBit .AND
@[expose] abbrev OR     {τ : OperationType} : Operation τ := .CompBit .OR
@[expose] abbrev XOR    {τ : OperationType} : Operation τ := .CompBit .XOR
@[expose] abbrev NOT    {τ : OperationType} : Operation τ := .CompBit .NOT
@[expose] abbrev BYTE   {τ : OperationType} : Operation τ := .CompBit .BYTE
@[expose] abbrev SHL    {τ : OperationType} : Operation τ := .CompBit .SHL
@[expose] abbrev SHR    {τ : OperationType} : Operation τ := .CompBit .SHR
@[expose] abbrev SAR    {τ : OperationType} : Operation τ := .CompBit .SAR

@[expose] abbrev KECCAK256 {τ : OperationType} : Operation τ := .Keccak .KECCAK256

@[expose] abbrev ADDRESS        {τ : OperationType} : Operation τ := .Env .ADDRESS
@[expose] abbrev BALANCE        {τ : OperationType} : Operation τ := .Env .BALANCE
@[expose] abbrev ORIGIN         {τ : OperationType} : Operation τ := .Env .ORIGIN
@[expose] abbrev CALLER         {τ : OperationType} : Operation τ := .Env .CALLER
@[expose] abbrev CALLVALUE      {τ : OperationType} : Operation τ := .Env .CALLVALUE
@[expose] abbrev CALLDATALOAD   {τ : OperationType} : Operation τ := .Env .CALLDATALOAD
@[expose] abbrev CALLDATASIZE   {τ : OperationType} : Operation τ := .Env .CALLDATASIZE
@[expose] abbrev CALLDATACOPY   {τ : OperationType} : Operation τ := .Env .CALLDATACOPY
@[expose] abbrev CODESIZE       {τ : OperationType} : Operation τ := .Env .CODESIZE
@[expose] abbrev GASPRICE       {τ : OperationType} : Operation τ := .Env .GASPRICE
@[expose] abbrev CODECOPY       {τ : OperationType} : Operation τ := .Env .CODECOPY
@[expose] abbrev EXTCODECOPY    {τ : OperationType} : Operation τ := .Env .EXTCODECOPY
@[expose] abbrev EXTCODESIZE    {τ : OperationType} : Operation τ := .Env .EXTCODESIZE
@[expose] abbrev RETURNDATASIZE {τ : OperationType} : Operation τ := .Env .RETURNDATASIZE
@[expose] abbrev RETURNDATACOPY {τ : OperationType} : Operation τ := .Env .RETURNDATACOPY
@[expose] abbrev EXTCODEHASH    {τ : OperationType} : Operation τ := .Env .EXTCODEHASH

@[expose] abbrev BLOCKHASH   {τ : OperationType} : Operation τ := .Block .BLOCKHASH
@[expose] abbrev COINBASE    {τ : OperationType} : Operation τ := .Block .COINBASE
@[expose] abbrev TIMESTAMP   {τ : OperationType} : Operation τ := .Block .TIMESTAMP
@[expose] abbrev NUMBER      {τ : OperationType} : Operation τ := .Block .NUMBER
@[expose] abbrev PREVRANDAO  {τ : OperationType} : Operation τ := .Block .PREVRANDAO
@[expose] abbrev GASLIMIT    {τ : OperationType} : Operation τ := .Block .GASLIMIT
@[expose] abbrev CHAINID     {τ : OperationType} : Operation τ := .Block .CHAINID
@[expose] abbrev SELFBALANCE {τ : OperationType} : Operation τ := .Block .SELFBALANCE
@[expose] abbrev BASEFEE     {τ : OperationType} : Operation τ := .Block .BASEFEE
@[expose] abbrev BLOBHASH    {τ : OperationType} : Operation τ := .Block .BLOBHASH
@[expose] abbrev BLOBBASEFEE {τ : OperationType} : Operation τ := .Block .BLOBBASEFEE

@[expose] abbrev POP     {τ : OperationType}   : Operation τ    := .StackMemFlow .POP
@[expose] abbrev MLOAD   {τ : OperationType}   : Operation τ    := .StackMemFlow .MLOAD
@[expose] abbrev MSTORE  {τ : OperationType}   : Operation τ    := .StackMemFlow .MSTORE
@[expose] abbrev SLOAD   {τ : OperationType}   : Operation τ    := .StackMemFlow .SLOAD
@[expose] abbrev SSTORE  {τ : OperationType}   : Operation τ    := .StackMemFlow .SSTORE
@[expose] abbrev MSTORE8 {τ : OperationType}   : Operation τ    := .StackMemFlow .MSTORE8
@[expose] abbrev JUMP                          : Operation .EVM := .StackMemFlow .JUMP
@[expose] abbrev JUMPI                         : Operation .EVM := .StackMemFlow .JUMPI
@[expose] abbrev PC                            : Operation .EVM    := .StackMemFlow .PC
@[expose] abbrev MSIZE   {τ : OperationType}   : Operation τ    := .StackMemFlow .MSIZE
@[expose] abbrev GAS     {τ : OperationType}   : Operation τ    := .StackMemFlow .GAS
@[expose] abbrev JUMPDEST                      : Operation .EVM := .StackMemFlow .JUMPDEST
@[expose] abbrev TLOAD   {τ : OperationType} : Operation τ    := .StackMemFlow .TLOAD
@[expose] abbrev TSTORE  {τ : OperationType} : Operation τ    := .StackMemFlow .TSTORE
@[expose] abbrev MCOPY   {τ : OperationType} : Operation τ := .StackMemFlow .MCOPY

@[expose] abbrev PUSH0  : Operation .EVM := .Push .PUSH0
@[expose] abbrev PUSH1  : Operation .EVM := .Push .PUSH1
@[expose] abbrev PUSH2  : Operation .EVM := .Push .PUSH2
@[expose] abbrev PUSH3  : Operation .EVM := .Push .PUSH3
@[expose] abbrev PUSH4  : Operation .EVM := .Push .PUSH4
@[expose] abbrev PUSH5  : Operation .EVM := .Push .PUSH5
@[expose] abbrev PUSH6  : Operation .EVM := .Push .PUSH6
@[expose] abbrev PUSH7  : Operation .EVM := .Push .PUSH7
@[expose] abbrev PUSH8  : Operation .EVM := .Push .PUSH8
@[expose] abbrev PUSH9  : Operation .EVM := .Push .PUSH9
@[expose] abbrev PUSH10 : Operation .EVM := .Push .PUSH10
@[expose] abbrev PUSH11 : Operation .EVM := .Push .PUSH11
@[expose] abbrev PUSH12 : Operation .EVM := .Push .PUSH12
@[expose] abbrev PUSH13 : Operation .EVM := .Push .PUSH13
@[expose] abbrev PUSH14 : Operation .EVM := .Push .PUSH14
@[expose] abbrev PUSH15 : Operation .EVM := .Push .PUSH15
@[expose] abbrev PUSH16 : Operation .EVM := .Push .PUSH16
@[expose] abbrev PUSH17 : Operation .EVM := .Push .PUSH17
@[expose] abbrev PUSH18 : Operation .EVM := .Push .PUSH18
@[expose] abbrev PUSH19 : Operation .EVM := .Push .PUSH19
@[expose] abbrev PUSH20 : Operation .EVM := .Push .PUSH20
@[expose] abbrev PUSH21 : Operation .EVM := .Push .PUSH21
@[expose] abbrev PUSH22 : Operation .EVM := .Push .PUSH22
@[expose] abbrev PUSH23 : Operation .EVM := .Push .PUSH23
@[expose] abbrev PUSH24 : Operation .EVM := .Push .PUSH24
@[expose] abbrev PUSH25 : Operation .EVM := .Push .PUSH25
@[expose] abbrev PUSH26 : Operation .EVM := .Push .PUSH26
@[expose] abbrev PUSH27 : Operation .EVM := .Push .PUSH27
@[expose] abbrev PUSH28 : Operation .EVM := .Push .PUSH28
@[expose] abbrev PUSH29 : Operation .EVM := .Push .PUSH29
@[expose] abbrev PUSH30 : Operation .EVM := .Push .PUSH30
@[expose] abbrev PUSH31 : Operation .EVM := .Push .PUSH31
@[expose] abbrev PUSH32 : Operation .EVM := .Push .PUSH32

@[expose] abbrev DUP1  : Operation .EVM := .Dup .DUP1
@[expose] abbrev DUP2  : Operation .EVM := .Dup .DUP2
@[expose] abbrev DUP3  : Operation .EVM := .Dup .DUP3
@[expose] abbrev DUP4  : Operation .EVM := .Dup .DUP4
@[expose] abbrev DUP5  : Operation .EVM := .Dup .DUP5
@[expose] abbrev DUP6  : Operation .EVM := .Dup .DUP6
@[expose] abbrev DUP7  : Operation .EVM := .Dup .DUP7
@[expose] abbrev DUP8  : Operation .EVM := .Dup .DUP8
@[expose] abbrev DUP9  : Operation .EVM := .Dup .DUP9
@[expose] abbrev DUP10 : Operation .EVM := .Dup .DUP10
@[expose] abbrev DUP11 : Operation .EVM := .Dup .DUP11
@[expose] abbrev DUP12 : Operation .EVM := .Dup .DUP12
@[expose] abbrev DUP13 : Operation .EVM := .Dup .DUP13
@[expose] abbrev DUP14 : Operation .EVM := .Dup .DUP14
@[expose] abbrev DUP15 : Operation .EVM := .Dup .DUP15
@[expose] abbrev DUP16 : Operation .EVM := .Dup .DUP16

@[expose] abbrev SWAP1  : Operation .EVM := .Exchange .SWAP1
@[expose] abbrev SWAP2  : Operation .EVM := .Exchange .SWAP2
@[expose] abbrev SWAP3  : Operation .EVM := .Exchange .SWAP3
@[expose] abbrev SWAP4  : Operation .EVM := .Exchange .SWAP4
@[expose] abbrev SWAP5  : Operation .EVM := .Exchange .SWAP5
@[expose] abbrev SWAP6  : Operation .EVM := .Exchange .SWAP6
@[expose] abbrev SWAP7  : Operation .EVM := .Exchange .SWAP7
@[expose] abbrev SWAP8  : Operation .EVM := .Exchange .SWAP8
@[expose] abbrev SWAP9  : Operation .EVM := .Exchange .SWAP9
@[expose] abbrev SWAP10 : Operation .EVM := .Exchange .SWAP10
@[expose] abbrev SWAP11 : Operation .EVM := .Exchange .SWAP11
@[expose] abbrev SWAP12 : Operation .EVM := .Exchange .SWAP12
@[expose] abbrev SWAP13 : Operation .EVM := .Exchange .SWAP13
@[expose] abbrev SWAP14 : Operation .EVM := .Exchange .SWAP14
@[expose] abbrev SWAP15 : Operation .EVM := .Exchange .SWAP15
@[expose] abbrev SWAP16 : Operation .EVM := .Exchange .SWAP16

@[expose] abbrev LOG0 {τ : OperationType} : Operation τ := .Log .LOG0
@[expose] abbrev LOG1 {τ : OperationType} : Operation τ := .Log .LOG1
@[expose] abbrev LOG2 {τ : OperationType} : Operation τ := .Log .LOG2
@[expose] abbrev LOG3 {τ : OperationType} : Operation τ := .Log .LOG3
@[expose] abbrev LOG4 {τ : OperationType} : Operation τ := .Log .LOG4

@[expose] abbrev CREATE       {τ : OperationType} : Operation τ := .System .CREATE
@[expose] abbrev CALL         {τ : OperationType} : Operation τ := .System .CALL
@[expose] abbrev CALLCODE     {τ : OperationType} : Operation τ := .System .CALLCODE
@[expose] abbrev RETURN       {τ : OperationType} : Operation τ := .System .RETURN
@[expose] abbrev DELEGATECALL {τ : OperationType} : Operation τ := .System .DELEGATECALL
@[expose] abbrev CREATE2      {τ : OperationType} : Operation τ := .System .CREATE2
@[expose] abbrev STATICCALL   {τ : OperationType} : Operation τ := .System .STATICCALL
@[expose] abbrev REVERT       {τ : OperationType} : Operation τ := .System .REVERT
@[expose] abbrev INVALID      {τ : OperationType} : Operation τ := .System .INVALID
@[expose] abbrev SELFDESTRUCT {τ : OperationType} : Operation τ := .System .SELFDESTRUCT

@[expose] def isPush {τ : OperationType} : Operation τ → Bool
  | .Push _ => true
  | _ => false

@[expose] def isJump {τ : OperationType} : Operation τ → Bool
  | .JUMP => true
  | .JUMPI => true
  | _ => false

@[expose] def isPC {τ : OperationType} : Operation τ → Bool
  | .PC => true
  | _ => false

@[expose] def isJumpdest {τ : OperationType} : Operation τ → Bool
  | .JUMPDEST => true
  | _ => false

@[expose] def isDup {τ : OperationType} : Operation τ → Bool
  | .Dup _ => true
  | _ => false

@[expose] def isSwap {τ : OperationType} : Operation τ → Bool
  | .Exchange _ => true
  | _ => false

@[expose] def isCreate {τ : OperationType} : Operation τ → Bool
  | .CREATE => true
  | .CREATE2 => true
  | _ => false

@[expose] def isCall {τ : OperationType} : Operation τ → Bool
  | .CALL => true
  | .CALLCODE => true
  | .DELEGATECALL => true
  | .STATICCALL => true
  | _ => false


end Operation

open EvmYul.UInt256

@[expose] def exp (a b : UInt256) : UInt256 :=
  a ^ b

@[expose] abbrev fromBool := Bool.toUInt256

@[expose] def lt (a b : UInt256) :=
  fromBool (a < b)

@[expose] def gt (a b : UInt256) :=
  fromBool (a > b)

-- def slt (a b : UInt256) :=
--   fromBool (EvmYul.UInt256.slt a b)

-- def sgt (a b : UInt256) :=
--   fromBool (EvmYul.UInt256.sgt a b)

@[expose] def eq (a b : UInt256) :=
  fromBool (a = b)

@[expose] def isZero (a : UInt256) :=
  fromBool (eq0 a)

end EvmYul

open EvmYul

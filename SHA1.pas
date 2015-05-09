{-------------------------------------------------------------------------------

  This Source Code Form is subject to the terms of the Mozilla Public
  License, v. 2.0. If a copy of the MPL was not distributed with this
  file, You can obtain one at http://mozilla.org/MPL/2.0/.

-------------------------------------------------------------------------------}
{===============================================================================

  SHA1 Hash Calculation

  ©František Milt 2015-05-07

  Version 1.1.1

===============================================================================}
unit SHA1;

{$DEFINE LargeBuffer}
{.$DEFINE UseStringStream}

{$IFOPT Q+}
  {$DEFINE OverflowCheck}
{$ENDIF}

interface

uses
  Classes;

type
{$IFDEF FPC}
  QuadWord = QWord;
{$ELSE}
  QuadWord = Int64;
{$ENDIF}
  PQuadWord = ^QuadWord;

{$IFDEF x64}
  PtrUInt = UInt64;
{$ELSE}
  PtrUInt = LongWord;
{$ENDIF}

  TSize = PtrUInt;

  TSHA1Hash = Record
    PartA:  LongWord;
    PartB:  LongWord;
    PartC:  LongWord;
    PartD:  LongWord;
    PartE:  LongWord;
  end;
  PSHA1Hash = ^TSHA1Hash;

const
  InitialSHA1: TSHA1Hash = (
    PartA:  $67452301;
    PartB:  $EFCDAB89;
    PartC:  $98BADCFE;
    PartD:  $10325476;
    PartE:  $C3D2E1F0);

  ZeroSHA1: TSHA1Hash = (PartA: 0; PartB: 0; PartC: 0; PartD: 0; PartE: 0);

Function SHA1toStr(Hash: TSHA1Hash): String;
Function StrToSHA1(Str: String): TSHA1Hash;
Function TryStrToSHA1(const Str: String; out Hash: TSHA1Hash): Boolean;
Function StrToSHA1Def(const Str: String; Default: TSHA1Hash): TSHA1Hash;
Function SameSHA1(A,B: TSHA1Hash): Boolean;

procedure BufferSHA1(var Hash: TSHA1Hash; const Buffer; Size: TSize); overload;
Function LastBufferSHA1(Hash: TSHA1Hash; const Buffer; Size: TSize; MessageLength: QuadWord): TSHA1Hash; overload;
Function LastBufferSHA1(Hash: TSHA1Hash; const Buffer; Size: TSize): TSHA1Hash; overload;

Function BufferSHA1(const Buffer; Size: TSize): TSHA1Hash; overload;

Function AnsiStringSHA1(const Str: AnsiString): TSHA1Hash;
Function WideStringSHA1(const Str: WideString): TSHA1Hash;
Function StringSHA1(const Str: String): TSHA1Hash;

Function StreamSHA1(Stream: TStream; Count: Int64 = -1): TSHA1Hash;
Function FileSHA1(const FileName: String): TSHA1Hash;

//------------------------------------------------------------------------------

type
  TSHA1Context = type Pointer;

Function SHA1_Init: TSHA1Context;
procedure SHA1_Update(Context: TSHA1Context; const Buffer; Size: TSize);
Function SHA1_Final(var Context: TSHA1Context; const Buffer; Size: TSize): TSHA1Hash; overload;
Function SHA1_Final(var Context: TSHA1Context): TSHA1Hash; overload;
Function SHA1_Hash(const Buffer; Size: TSize): TSHA1Hash;


implementation

uses
  SysUtils, Math;

const
  BlockSize       = 64;                           // 512 bits
{$IFDEF LargeBuffers}
  BlocksPerBuffer = 16384;                        // 1MiB BufferSize
{$ELSE}
  BlocksPerBuffer = 64;                           // 4KiB BufferSize
{$ENDIF}
  BufferSize      = BlocksPerBuffer * BlockSize;  // size of read buffer

  RoundConsts: Array[0..3] of LongWord = ($5A827999, $6ED9EBA1, $8F1BBCDC, $CA62C1D6);

type
  TBlockBuffer = Array[0..BlockSize - 1] of Byte;
  PBlockBuffer = ^TBlockBuffer;

  TSHA1Context_Internal = record
    MessageHash:    TSHA1Hash;
    MessageLength:  QuadWord;
    TransferSize:   LongWord;
    TransferBuffer: TBlockBuffer;
  end;
  PSHA1Context_Internal = ^TSHA1Context_Internal;

//==============================================================================

{$IFDEF FPC}{$ASMMODE intel}{$ENDIF}

Function EndianSwap(Value: LongWord): LongWord;{$IFNDEF PurePascal}assembler;{$ENDIF} overload;
{$IFDEF PurePascal}
begin
Result := LongWord((Value and $000000FF shl 24) or (Value and $0000FF00 shl 8) or
                   (Value and $00FF0000 shr 8) or (Value and $FF000000 shr 24));
end;
{$ELSE}
asm
{$IFDEF x64}
    MOV   RAX,  RCX
{$ENDIF}
    BSWAP EAX
end;
{$ENDIF}

//------------------------------------------------------------------------------

Function EndianSwap(Value: QuadWord): QuadWord;{$IFNDEF PurePascal}assembler;{$ENDIF} overload;
{$IFDEF PurePascal}
begin
Int64Rec(Result).Hi := EndianSwap(Int64Rec(Value).Lo);
Int64Rec(Result).Lo := EndianSwap(Int64Rec(Value).Hi);
end;
{$ELSE}
asm
{$IFDEF x64}
    MOV   RAX,  RCX
    BSWAP RAX
{$ELSE}
    MOV   EAX,  dword ptr [Value + 4]
    MOV   EDX,  dword ptr [Value]
    BSWAP EAX
    BSWAP EDX
{$ENDIF}
end;
{$ENDIF}

//------------------------------------------------------------------------------

Function LeftRotate(Value: LongWord; Shift: Byte): LongWord;{$IFNDEF PurePascal}assembler;{$ENDIF}
{$IFDEF PurePascal}
begin
Shift := Shift and $1F;
Result := LongWord((Value shl Shift) or (Value shr (32 - Shift)));
end;
{$ELSE}
asm
{$IFDEF x64}
    MOV   EAX,  ECX
{$ENDIF}
    MOV   CL,   DL
    ROL   EAX,  CL
end;
{$ENDIF}

//==============================================================================

Function BlockHash(Hash: TSHA1Hash; const Block): TSHA1Hash;
var
  i:              Integer;
  Temp:           LongWord;
  FuncResult:     LongWord;
  RoundConstant:  LongWord;
  State:          Array[0..79] of LongWord;  
  BlockWords:     Array[0..15] of LongWord absolute Block;
begin
Result := Hash;
For i := 0 to 15 do State[i] := EndianSwap(BlockWords[i]);
For i := 16 to 79 do State[i] := LeftRotate(State[i - 3] xor State[i - 8] xor State[i - 14] xor State[i - 16],1);
For i := 0 to 79 do
  begin
    case i of
       0..19: begin
                FuncResult := (Hash.PartB and Hash.PartC) or ((not Hash.PartB) and Hash.PartD);
                RoundConstant := RoundConsts[0];
              end;
      20..39: begin
                FuncResult := Hash.PartB xor Hash.PartC xor Hash.PartD;
                RoundConstant := RoundConsts[1];
              end;
      40..59: begin
                FuncResult := (Hash.PartB and Hash.PartC) or (Hash.PartB and Hash.PartD) or (Hash.PartC and Hash.PartD);
                RoundConstant := RoundConsts[2];
              end;
    else
     {60..79:}  FuncResult := Hash.PartB xor Hash.PartC xor Hash.PartD;
                RoundConstant := RoundConsts[3];
    end;
    {$IFDEF OverflowCheck}{$Q-}{$ENDIF}
    Temp := LongWord(LeftRotate(Hash.PartA,5) + FuncResult + Hash.PartE + RoundConstant + State[i]);
    {$IFDEF OverflowCheck}{$Q+}{$ENDIF}
    Hash.PartE := Hash.PartD;
    Hash.PartD := Hash.PartC;
    Hash.PartC := LeftRotate(Hash.PartB,30);
    Hash.PartB := Hash.PartA;
    Hash.PartA := Temp;
  end;
{$IFDEF OverflowCheck}{$Q-}{$ENDIF}
Result.PartA := LongWord(Result.PartA + Hash.PartA);
Result.PartB := LongWord(Result.PartB + Hash.PartB);
Result.PartC := LongWord(Result.PartC + Hash.PartC);
Result.PartD := LongWord(Result.PartD + Hash.PartD);
Result.PartE := LongWord(Result.PartE + Hash.PartE);
{$IFDEF OverflowCheck}{$Q+}{$ENDIF}
end;

//==============================================================================

Function SHA1toStr(Hash: TSHA1Hash): String;
begin
Result := IntToHex(Hash.PartA,8) + IntToHex(Hash.PartB,8) +
          IntToHex(Hash.PartC,8) + IntToHex(Hash.PartD,8) +
          IntToHex(Hash.PartE,8);
end;

//------------------------------------------------------------------------------

Function StrToSHA1(Str: String): TSHA1Hash;
begin
If Length(Str) < 40 then
  Str := StringOfChar('0',40 - Length(Str)) + Str
else
  If Length(Str) > 40 then
    Str := Copy(Str,Length(Str) - 39,40);
Result.PartA := StrToInt('$' + Copy(Str,1,8));
Result.PartB := StrToInt('$' + Copy(Str,9,8));
Result.PartC := StrToInt('$' + Copy(Str,17,8));
Result.PartD := StrToInt('$' + Copy(Str,25,8));
Result.PartE := StrToInt('$' + Copy(Str,33,8));
end;

//------------------------------------------------------------------------------

Function TryStrToSHA1(const Str: String; out Hash: TSHA1Hash): Boolean;
begin
try
  Hash := StrToSHA1(Str);
  Result := True;
except
  Result := False;
end;
end;

//------------------------------------------------------------------------------

Function StrToSHA1Def(const Str: String; Default: TSHA1Hash): TSHA1Hash;
begin
If not TryStrToSHA1(Str,Result) then
  Result := Default;
end;

//------------------------------------------------------------------------------

Function SameSHA1(A,B: TSHA1Hash): Boolean;
begin
Result := (A.PartA = B.PartA) and (A.PartB = B.PartB) and
          (A.PartC = B.PartC) and (A.PartD = B.PartD) and
          (A.PartE = B.PartE);
end;

//==============================================================================

procedure BufferSHA1(var Hash: TSHA1Hash; const Buffer; Size: TSize);
var
  i:    TSize;
  Buff: PBlockBuffer;
begin
If Size > 0 then
  begin
    If (Size mod BlockSize) = 0 then
      begin
        Buff := @Buffer;
        For i := 0 to Pred(Size div BlockSize) do
          begin
            Hash := BlockHash(Hash,Buff^);
            Inc(Buff);
          end;
      end
    else raise Exception.CreateFmt('BufferSHA1: Buffer size is not divisible by %d.',[BlockSize]);
  end;
end;

//------------------------------------------------------------------------------

Function LastBufferSHA1(Hash: TSHA1Hash; const Buffer; Size: TSize; MessageLength: QuadWord): TSHA1Hash;
var
  FullBlocks:     TSize;
  LastBlockSize:  TSize;
  HelpBlocks:     TSize;
  HelpBlocksBuff: Pointer;
begin
Result := Hash;
FullBlocks := Size div BlockSize;
If FullBlocks > 0 then BufferSHA1(Result,Buffer,FullBlocks * BlockSize);
{$IFDEF x64}
LastBlockSize := Size - (FullBlocks * BlockSize);
{$ELSE}
LastBlockSize := Size - (Int64(FullBlocks) * BlockSize);
{$ENDIF}
HelpBlocks := Ceil((LastBlockSize + SizeOf(QuadWord) + 1) / BlockSize);
HelpBlocksBuff := AllocMem(HelpBlocks * BlockSize);
try
  Move({%H-}Pointer(PtrUInt(@Buffer) + (FullBlocks * BlockSize))^,HelpBlocksBuff^,LastBlockSize);
  {%H-}PByte(PtrUInt(HelpBlocksBuff) + LastBlockSize)^ := $80;
  {$IFDEF x64}
  {%H-}PQuadWord(PtrUInt(HelpBlocksBuff) + (HelpBlocks * BlockSize) - SizeOf(QuadWord))^ := EndianSwap(MessageLength);
  {$ELSE}
  {%H-}PQuadWord(PtrUInt(HelpBlocksBuff) + (Int64(HelpBlocks) * BlockSize) - SizeOf(QuadWord))^ := EndianSwap(MessageLength);
  {$ENDIF}
  BufferSHA1(Result,HelpBlocksBuff^,HelpBlocks * BlockSize);
finally
  FreeMem(HelpBlocksBuff,HelpBlocks * BlockSize);
end;
end;

//------------------------------------------------------------------------------

Function LastBufferSHA1(Hash: TSHA1Hash; const Buffer; Size: TSize): TSHA1Hash;
begin
Result := LastBufferSHA1(Hash,Buffer,Size,Size shl 3);
end;

//==============================================================================

Function BufferSHA1(const Buffer; Size: TSize): TSHA1Hash;
begin
Result := LastBufferSHA1(InitialSHA1,Buffer,Size);
end;

//==============================================================================

Function AnsiStringSHA1(const Str: AnsiString): TSHA1Hash;
{$IFDEF UseStringStream}
var
  StringStream: TStringStream;
begin
StringStream := TStringStream.Create(Str);
try
  Result := StreamSHA1(StringStream);
finally
  StringStream.Free;
end;
end;
{$ELSE}
begin
Result := BufferSHA1(PAnsiChar(Str)^,Length(Str) * SizeOf(AnsiChar));
end;
{$ENDIF}

//------------------------------------------------------------------------------

Function WideStringSHA1(const Str: WideString): TSHA1Hash;
{$IFDEF UseStringStream}
var
  StringStream: TStringStream;
begin
StringStream := TStringStream.Create(Str);
try
  Result := StreamSHA1(StringStream);
finally
  StringStream.Free;
end;
end;
{$ELSE}
begin
Result := BufferSHA1(PWideChar(Str)^,Length(Str) * SizeOf(WideChar));
end;
{$ENDIF}

//------------------------------------------------------------------------------

Function StringSHA1(const Str: String): TSHA1Hash;
{$IFDEF UseStringStream}
var
  StringStream: TStringStream;
begin
StringStream := TStringStream.Create(Str);
try
  Result := StreamSHA1(StringStream);
finally
  StringStream.Free;
end;
end;
{$ELSE}
begin
Result := BufferSHA1(PChar(Str)^,Length(Str) * SizeOf(Char));
end;
{$ENDIF}

//==============================================================================

Function StreamSHA1(Stream: TStream; Count: Int64 = -1): TSHA1Hash;
var
  Buffer:         Pointer;
  BytesRead:      Integer;
  MessageLength:  QuadWord;
begin
If Assigned(Stream) then
  begin
    If Count = 0 then
      Count := Stream.Size - Stream.Position;
    If Count < 0 then
      begin
        Stream.Position := 0;
        Count := Stream.Size;
      end;
    MessageLength := QuadWord(Count shl 3);
    GetMem(Buffer,BufferSize);
    try
      Result := InitialSHA1;
      repeat
        BytesRead := Stream.Read(Buffer^,Min(BufferSize,Count));
        If BytesRead < BufferSize then
          Result := LastBufferSHA1(Result,Buffer^,BytesRead,MessageLength)
        else
          BufferSHA1(Result,Buffer^,BytesRead);
        Dec(Count,BytesRead);
      until BytesRead < BufferSize;
    finally
      FreeMem(Buffer,BufferSize);
    end;
  end
else raise Exception.Create('StreamSHA1: Stream is not assigned.');
end;

//------------------------------------------------------------------------------

Function FileSHA1(const FileName: String): TSHA1Hash;
var
  FileStream: TFileStream;
begin
FileStream := TFileStream.Create(FileName, fmOpenRead or fmShareDenyWrite);
try
  Result := StreamSHA1(FileStream);
finally
  FileStream.Free;
end;
end;

//==============================================================================

Function SHA1_Init: TSHA1Context;
begin
Result := AllocMem(SizeOf(TSHA1Context_Internal));
with PSHA1Context_Internal(Result)^ do
  begin
    MessageHash := InitialSHA1;
    MessageLength := 0;
    TransferSize := 0;
  end;
end;

//------------------------------------------------------------------------------

procedure SHA1_Update(Context: TSHA1Context; const Buffer; Size: TSize);
var
  FullBlocks:     TSize;
  RemainingSize:  TSize;
begin
with PSHA1Context_Internal(Context)^ do
  begin
    If TransferSize > 0 then
      begin
        If Size >= (BlockSize - TransferSize) then
          begin
            Inc(MessageLength,(BlockSize - TransferSize) shl 3);
            Move(Buffer,TransferBuffer[TransferSize],BlockSize - TransferSize);
            BufferSHA1(MessageHash,TransferBuffer,BlockSize);
            RemainingSize := Size - (BlockSize - TransferSize);
            TransferSize := 0;
            SHA1_Update(Context,{%H-}Pointer(PtrUInt(@Buffer) + (Size - RemainingSize))^,RemainingSize);
          end
        else
          begin
            Inc(MessageLength,Size shl 3);
            Move(Buffer,TransferBuffer[TransferSize],Size);
            Inc(TransferSize,Size);
          end;  
      end
    else
      begin
        Inc(MessageLength,Size shl 3);
        FullBlocks := Size div BlockSize;
        BufferSHA1(MessageHash,Buffer,FullBlocks * BlockSize);
        If (FullBlocks * BlockSize) < Size then
          begin
            {$IFDEF x64}
            TransferSize := Size - (FullBlocks * BlockSize);
            {$ELSE}
            TransferSize := Size - (Int64(FullBlocks) * BlockSize);
            {$ENDIF}
            Move({%H-}Pointer(PtrUInt(@Buffer) + (Size - TransferSize))^,TransferBuffer,TransferSize);
          end;
      end;
  end;
end;

//------------------------------------------------------------------------------

Function SHA1_Final(var Context: TSHA1Context; const Buffer; Size: TSize): TSHA1Hash;
begin
SHA1_Update(Context,Buffer,Size);
Result := SHA1_Final(Context);
end;

//------------------------------------------------------------------------------

Function SHA1_Final(var Context: TSHA1Context): TSHA1Hash;
begin
with PSHA1Context_Internal(Context)^ do
  Result := LastBufferSHA1(MessageHash,TransferBuffer,TransferSize,MessageLength);
FreeMem(Context,SizeOf(TSHA1Context_Internal));
Context := nil;
end;

//------------------------------------------------------------------------------

Function SHA1_Hash(const Buffer; Size: TSize): TSHA1Hash;
begin
Result := LastBufferSHA1(InitialSHA1,Buffer,Size);
end;

end.

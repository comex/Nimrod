/* Generated by Nimrod Compiler v0.8.9 */
/*   (c) 2010 Andreas Rumpf */

typedef long int NI;
typedef unsigned long int NU;
#include "nimbase.h"

typedef struct TY38019 TY38019;
typedef struct TNimType TNimType;
typedef struct TNimNode TNimNode;
typedef struct TY38013 TY38013;
typedef struct NimStringDesc NimStringDesc;
typedef struct TGenericSeq TGenericSeq;
typedef struct TY10602 TY10602;
typedef struct TY8004 TY8004;
typedef struct TY10990 TY10990;
typedef struct TY10618 TY10618;
typedef struct TY10614 TY10614;
typedef struct TY10610 TY10610;
typedef struct TY10988 TY10988;
typedef struct TY40008 TY40008;
typedef struct TY4377 TY4377;
typedef struct TY33378 TY33378;
typedef struct E_Base E_Base;
typedef struct TNimObject TNimObject;
typedef struct TSafePoint TSafePoint;
typedef struct TY38015 TY38015;
typedef struct TY40006 TY40006;
typedef struct TY40004 TY40004;
struct TNimType {
NI size;
NU8 kind;
NU8 flags;
TNimType* base;
TNimNode* node;
void* finalizer;
};
struct TY38019 {
TNimType* m_type;
TY38013* Head;
TY38013* Tail;
NI Counter;
};
struct TNimNode {
NU8 kind;
NI offset;
TNimType* typ;
NCSTRING name;
NI len;
TNimNode** sons;
};
struct TGenericSeq {
NI len;
NI space;
};
typedef NIM_CHAR TY239[100000001];
struct NimStringDesc {
  TGenericSeq Sup;
TY239 data;
};
struct TY10602 {
NI Refcount;
TNimType* Typ;
};
typedef N_STDCALL_PTR(void, TY8016) (TY8004* L_8018);
struct TY10618 {
NI Len;
NI Cap;
TY10602** D;
};
struct TY10614 {
NI Counter;
NI Max;
TY10610* Head;
TY10610** Data;
};
struct TY8004 {
void* Debuginfo;
NI32 Lockcount;
NI32 Recursioncount;
NI Owningthread;
NI Locksemaphore;
NI32 Reserved;
};
struct TY10988 {
NI Stackscans;
NI Cyclecollections;
NI Maxthreshold;
NI Maxstacksize;
NI Maxstackcells;
NI Cycletablesize;
};
struct TY10990 {
TY10618 Zct;
TY10618 Decstack;
TY10614 Cycleroots;
TY10618 Tempstack;
TY8004 Cyclerootslock;
TY8004 Zctlock;
TY10988 Stat;
};
typedef N_STDCALL_PTR(void, TY8020) (TY8004* L_8022);
struct TY33378 {
NimStringDesc* Head;
NimStringDesc* Tail;
};
typedef NimStringDesc* TY41252[4];
typedef NimStringDesc* TY41272[3];
struct TNimObject {
TNimType* m_type;
};
struct E_Base {
  TNimObject Sup;
E_Base* parent;
NCSTRING name;
NimStringDesc* message;
};
struct TSafePoint {
TSafePoint* prev;
NI status;
E_Base* exc;
jmp_buf context;
};
struct TY38013 {
  TNimObject Sup;
TY38013* Prev;
TY38013* Next;
};
struct TY38015 {
  TY38013 Sup;
NimStringDesc* Data;
};
typedef NimStringDesc* TY41352[1];
typedef NI TY8614[16];
struct TY10610 {
TY10610* Next;
NI Key;
TY8614 Bits;
};
struct TY40004 {
NimStringDesc* Key;
NimStringDesc* Val;
};
struct TY40008 {
  TNimObject Sup;
NI Counter;
TY40006* Data;
NU8 Mode;
};
struct TY4377 {
  TGenericSeq Sup;
  NimStringDesc* data[SEQ_DECL_SIZE];
};
struct TY40006 {
  TGenericSeq Sup;
  TY40004 data[SEQ_DECL_SIZE];
};
static N_INLINE(void, asgnRefNoCycle)(void** Dest_11818, void* Src_11819);
static N_INLINE(TY10602*, Usrtocell_11036)(void* Usr_11038);
static N_INLINE(NI, Atomicinc_3001)(NI* Memloc_3004, NI X_3005);
static N_INLINE(NI, Atomicdec_3006)(NI* Memloc_3009, NI X_3010);
static N_INLINE(void, Rtladdzct_11658)(TY10602* C_11660);
N_NOINLINE(void, Addzct_11025)(TY10618* S_11028, TY10602* C_11029);
N_NIMCALL(NimStringDesc*, copyString)(NimStringDesc* Src_17308);
N_NIMCALL(void*, newSeq)(TNimType* Typ_12804, NI Len_12805);
N_NIMCALL(NIM_BOOL, Existsconfigvar_41129)(NimStringDesc* Key_41131);
N_NIMCALL(NIM_BOOL, Haskey_40033)(TY40008* T_40035, NimStringDesc* Key_40036);
N_NIMCALL(NimStringDesc*, Getconfigvar_41132)(NimStringDesc* Key_41134);
N_NIMCALL(NimStringDesc*, Get_40029)(TY40008* T_40031, NimStringDesc* Key_40032);
N_NIMCALL(void, Setconfigvar_41135)(NimStringDesc* Key_41137, NimStringDesc* Val_41138);
N_NIMCALL(void, Put_40024)(TY40008* T_40026, NimStringDesc* Key_40027, NimStringDesc* Val_40028);
N_NIMCALL(NimStringDesc*, Getoutfile_41142)(NimStringDesc* Filename_41144, NimStringDesc* Ext_41145);
N_NIMCALL(NimStringDesc*, nosChangeFileExt)(NimStringDesc* Filename_33820, NimStringDesc* Ext_33821);
N_NIMCALL(void, Addimplicitmod_41139)(NimStringDesc* Filename_41141);
static N_INLINE(NI, addInt)(NI A_5803, NI B_5804);
N_NOINLINE(void, raiseOverflow)(void);
N_NIMCALL(TGenericSeq*, setLengthSeq)(TGenericSeq* Seq_17603, NI Elemsize_17604, NI Newlen_17605);
N_NOINLINE(void, raiseIndexError)(void);
N_NIMCALL(NimStringDesc*, Getprefixdir_41106)(void);
N_NIMCALL(void, nosSplitPath)(NimStringDesc* Path_33377, TY33378* Result);
N_NIMCALL(NimStringDesc*, nosgetApplicationDir)(void);
N_NIMCALL(NimStringDesc*, Shortendir_41197)(NimStringDesc* Dir_41199);
static N_INLINE(void, appendString)(NimStringDesc* Dest_17392, NimStringDesc* Src_17393);
static N_INLINE(void, appendChar)(NimStringDesc* Dest_17409, NIM_CHAR C_17410);
N_NIMCALL(NimStringDesc*, rawNewString)(NI Space_17287);
N_NIMCALL(NIM_BOOL, nsuStartsWith)(NimStringDesc* S_24769, NimStringDesc* Prefix_24770);
N_NIMCALL(NimStringDesc*, copyStr)(NimStringDesc* S_1924, NI First_1925);
N_NIMCALL(NimStringDesc*, nosgetCurrentDir)(void);
N_NIMCALL(NimStringDesc*, Removetrailingdirsep_41221)(NimStringDesc* Path_41223);
static N_INLINE(NI, subInt)(NI A_6003, NI B_6004);
N_NIMCALL(NimStringDesc*, copyStrLast)(NimStringDesc* S_1928, NI First_1929, NI Last_1930);
N_NIMCALL(NimStringDesc*, Togeneratedfile_41102)(NimStringDesc* Path_41104, NimStringDesc* Ext_41105);
N_NIMCALL(NimStringDesc*, nosJoinPathOpenArray)(NimStringDesc** Parts_33287, NI Parts_33287Len0);
N_NIMCALL(NimStringDesc*, Completegeneratedfilepath_41098)(NimStringDesc* F_41100, NIM_BOOL Createsubdir_41101);
static N_INLINE(void, pushSafePoint)(TSafePoint* S_4635);
N_NIMCALL(void, noscreateDir)(NimStringDesc* Dir_35403);
static N_INLINE(void, popSafePoint)(void);
static N_INLINE(E_Base*, getCurrentException)(void);
static N_INLINE(void, popCurrentException)(void);
static N_INLINE(void, asgnRef)(void** Dest_11814, void* Src_11815);
static N_INLINE(void, Incref_11802)(TY10602* C_11804);
static N_INLINE(NIM_BOOL, Canbecycleroot_11040)(TY10602* C_11042);
static N_INLINE(void, Rtladdcycleroot_11652)(TY10602* C_11654);
N_NOINLINE(void, Incl_10874)(TY10614* S_10877, TY10602* Cell_10878);
static N_INLINE(void, Decref_11664)(TY10602* C_11666);
N_NIMCALL(void, reraiseException)(void);
N_NIMCALL(NimStringDesc*, nosJoinPath)(NimStringDesc* Head_33203, NimStringDesc* Tail_33204);
N_NIMCALL(NimStringDesc*, Rawfindfile_41293)(NimStringDesc* F_41295);
N_NIMCALL(NIM_BOOL, nosexistsFile)(NimStringDesc* Filename_31804);
N_NIMCALL(void, chckObj)(TNimType* Obj_5575, TNimType* Subclass_5576);
N_NIMCALL(NimStringDesc*, Findfile_41087)(NimStringDesc* F_41089);
N_NIMCALL(NimStringDesc*, nsuToLowerStr)(NimStringDesc* S_23448);
N_NIMCALL(NI, Binarystrsearch_41146)(NimStringDesc** X_41149, NI X_41149Len0, NimStringDesc* Y_41150);
static N_INLINE(NI, divInt)(NI A_6403, NI B_6404);
N_NOINLINE(void, raiseDivByZero)(void);
N_NIMCALL(NI, nsuCmpIgnoreCase)(NimStringDesc* A_23595, NimStringDesc* B_23596);
N_NIMCALL(TY40008*, Newstringtable_40019)(NimStringDesc** Keyvaluepairs_40022, NI Keyvaluepairs_40022Len0, NU8 Mode_40023);
N_NIMCALL(void, Writeln_41286)(FILE* F_41289, NimStringDesc* X_41290);
N_NIMCALL(void, Write_3658)(FILE* F_3660, NimStringDesc* S_3661);
NIM_CONST NU32 Checksoptions_41072 = 1022;
STRING_LITERAL(TMP41086, "", 0);
STRING_LITERAL(TMP41254, "nimcache", 8);
STRING_LITERAL(TMP41292, "cannot create directory: ", 25);
STRING_LITERAL(TMP41353, "\015\012", 2);
NU32 Goptions_41075;
NU32 Gglobaloptions_41077;
NI8 Gexitcode_41078;
TY38019 Searchpaths_41079;
extern TNimType* NTI38019; /* TLinkedList */
NimStringDesc* Outfile_41080;
extern TY8016 Dl_8015;
extern TY10990 Gch_11010;
extern TY8020 Dl_8019;
NimStringDesc* Gindexfile_41081;
NU8 Gcmd_41082;
NI Gverbosity_41083;
NI Gnumberofprocessors_41084;
TY40008* Gconfigvars_41108;
NimStringDesc* Libpath_41109;
NimStringDesc* Projectpath_41110;
NIM_BOOL Gkeepcomments_41111;
TY4377* Gimplicitmods_41128;
extern TNimType* NTI4377; /* seq[string] */
extern TSafePoint* excHandler;
extern TNimType* NTI422; /* EOS */
extern E_Base* Currexception_4632;
extern TNimType* NTI38015; /* TStrEntry */
static N_INLINE(TY10602*, Usrtocell_11036)(void* Usr_11038) {
TY10602* Result_11039;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "usrToCell";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/gc.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_11039 = 0;
F.line = 100;F.filename = "gc.nim";
Result_11039 = ((TY10602*) ((NI32)((NU32)(((NI) (Usr_11038))) - (NU32)(((NI) (((NI)sizeof(TY10602))))))));
framePtr = framePtr->prev;
return Result_11039;
}
static N_INLINE(NI, Atomicinc_3001)(NI* Memloc_3004, NI X_3005) {
NI Result_7408;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "atomicInc";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/systhread.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_7408 = 0;
F.line = 29;F.filename = "systhread.nim";
Result_7408 = __sync_add_and_fetch(Memloc_3004, X_3005);
framePtr = framePtr->prev;
return Result_7408;
}
static N_INLINE(NI, Atomicdec_3006)(NI* Memloc_3009, NI X_3010) {
NI Result_7606;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "atomicDec";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/systhread.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_7606 = 0;
F.line = 37;F.filename = "systhread.nim";
Result_7606 = __sync_sub_and_fetch(Memloc_3009, X_3010);
framePtr = framePtr->prev;
return Result_7606;
}
static N_INLINE(void, Rtladdzct_11658)(TY10602* C_11660) {
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "rtlAddZCT";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/gc.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 211;F.filename = "gc.nim";
if (!NIM_TRUE) goto LA2;
F.line = 211;F.filename = "gc.nim";
Dl_8015(&Gch_11010.Zctlock);
LA2: ;
F.line = 212;F.filename = "gc.nim";
Addzct_11025(&Gch_11010.Zct, C_11660);
F.line = 213;F.filename = "gc.nim";
if (!NIM_TRUE) goto LA5;
F.line = 213;F.filename = "gc.nim";
Dl_8019(&Gch_11010.Zctlock);
LA5: ;
framePtr = framePtr->prev;
}
static N_INLINE(void, asgnRefNoCycle)(void** Dest_11818, void* Src_11819) {
TY10602* C_11820;
NI LOC4;
TY10602* C_11822;
NI LOC9;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "asgnRefNoCycle";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/gc.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 244;F.filename = "gc.nim";
if (!!((Src_11819 == NIM_NIL))) goto LA2;
C_11820 = 0;
F.line = 245;F.filename = "gc.nim";
C_11820 = Usrtocell_11036(Src_11819);
F.line = 246;F.filename = "gc.nim";
LOC4 = Atomicinc_3001(&(*C_11820).Refcount, 8);
LA2: ;
F.line = 247;F.filename = "gc.nim";
if (!!(((*Dest_11818) == NIM_NIL))) goto LA6;
C_11822 = 0;
F.line = 248;F.filename = "gc.nim";
C_11822 = Usrtocell_11036((*Dest_11818));
F.line = 249;F.filename = "gc.nim";
LOC9 = Atomicdec_3006(&(*C_11822).Refcount, 8);
if (!((NU32)(LOC9) < (NU32)(8))) goto LA10;
F.line = 250;F.filename = "gc.nim";
Rtladdzct_11658(C_11822);
LA10: ;
LA6: ;
F.line = 251;F.filename = "gc.nim";
(*Dest_11818) = Src_11819;
framePtr = framePtr->prev;
}
N_NIMCALL(NIM_BOOL, Existsconfigvar_41129)(NimStringDesc* Key_41131) {
NIM_BOOL Result_41154;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "existsConfigVar";
F.prev = framePtr;
F.filename = "rod/options.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_41154 = 0;
F.line = 110;F.filename = "options.nim";
Result_41154 = Haskey_40033(Gconfigvars_41108, Key_41131);
framePtr = framePtr->prev;
return Result_41154;
}
N_NIMCALL(NimStringDesc*, Getconfigvar_41132)(NimStringDesc* Key_41134) {
NimStringDesc* Result_41158;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "getConfigVar";
F.prev = framePtr;
F.filename = "rod/options.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_41158 = 0;
F.line = 113;F.filename = "options.nim";
Result_41158 = Get_40029(Gconfigvars_41108, Key_41134);
framePtr = framePtr->prev;
return Result_41158;
}
N_NIMCALL(void, Setconfigvar_41135)(NimStringDesc* Key_41137, NimStringDesc* Val_41138) {
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "setConfigVar";
F.prev = framePtr;
F.filename = "rod/options.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 116;F.filename = "options.nim";
Put_40024(Gconfigvars_41108, Key_41137, Val_41138);
framePtr = framePtr->prev;
}
N_NIMCALL(NimStringDesc*, Getoutfile_41142)(NimStringDesc* Filename_41144, NimStringDesc* Ext_41145) {
NimStringDesc* Result_41167;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "getOutFile";
F.prev = framePtr;
F.filename = "rod/options.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_41167 = 0;
F.line = 119;F.filename = "options.nim";
if (!!(((Outfile_41080) && (Outfile_41080)->Sup.len == 0))) goto LA2;
F.line = 119;F.filename = "options.nim";
Result_41167 = copyString(Outfile_41080);
goto LA1;
LA2: ;
F.line = 120;F.filename = "options.nim";
Result_41167 = nosChangeFileExt(Filename_41144, Ext_41145);
LA1: ;
framePtr = framePtr->prev;
return Result_41167;
}
static N_INLINE(NI, addInt)(NI A_5803, NI B_5804) {
NI Result_5805;
NIM_BOOL LOC2;
Result_5805 = 0;
Result_5805 = (NI32)((NU32)(A_5803) + (NU32)(B_5804));
LOC2 = (0 <= (NI32)(Result_5805 ^ A_5803));
if (LOC2) goto LA3;
LOC2 = (0 <= (NI32)(Result_5805 ^ B_5804));
LA3: ;
if (!LOC2) goto LA4;
goto BeforeRet;
LA4: ;
raiseOverflow();
BeforeRet: ;
return Result_5805;
}
N_NIMCALL(void, Addimplicitmod_41139)(NimStringDesc* Filename_41141) {
NI Length_41171;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "addImplicitMod";
F.prev = framePtr;
F.filename = "rod/options.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Length_41171 = 0;
F.line = 124;F.filename = "options.nim";
Length_41171 = Gimplicitmods_41128->Sup.len;
F.line = 125;F.filename = "options.nim";
Gimplicitmods_41128 = (TY4377*) setLengthSeq(&(Gimplicitmods_41128)->Sup, sizeof(NimStringDesc*), addInt(Length_41171, 1));
F.line = 126;F.filename = "options.nim";
if ((NU)(Length_41171) >= (NU)(Gimplicitmods_41128->Sup.len)) raiseIndexError();
asgnRefNoCycle((void**) &Gimplicitmods_41128->data[Length_41171], copyString(Filename_41141));
framePtr = framePtr->prev;
}
N_NIMCALL(NimStringDesc*, Getprefixdir_41106)(void) {
NimStringDesc* Result_41196;
NimStringDesc* LOC1;
TY33378 LOC2;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "getPrefixDir";
F.prev = framePtr;
F.filename = "rod/options.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_41196 = 0;
F.line = 129;F.filename = "options.nim";
LOC1 = 0;
LOC1 = nosgetApplicationDir();
memset((void*)&LOC2, 0, sizeof(LOC2));
nosSplitPath(LOC1, &LOC2);
Result_41196 = copyString(LOC2.Head);
framePtr = framePtr->prev;
return Result_41196;
}
static N_INLINE(void, appendString)(NimStringDesc* Dest_17392, NimStringDesc* Src_17393) {
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "appendString";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/sysstr.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 150;F.filename = "sysstr.nim";
memcpy(((NCSTRING) (&(*Dest_17392).data[((*Dest_17392).Sup.len)-0])), ((NCSTRING) ((*Src_17393).data)), ((NI32) ((NI32)((NI32)((*Src_17393).Sup.len + 1) * 1))));
F.line = 151;F.filename = "sysstr.nim";
(*Dest_17392).Sup.len += (*Src_17393).Sup.len;
framePtr = framePtr->prev;
}
static N_INLINE(void, appendChar)(NimStringDesc* Dest_17409, NIM_CHAR C_17410) {
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "appendChar";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/sysstr.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 154;F.filename = "sysstr.nim";
(*Dest_17409).data[((*Dest_17409).Sup.len)-0] = C_17410;
F.line = 155;F.filename = "sysstr.nim";
(*Dest_17409).data[((NI32)((*Dest_17409).Sup.len + 1))-0] = 0;
F.line = 156;F.filename = "sysstr.nim";
(*Dest_17409).Sup.len += 1;
framePtr = framePtr->prev;
}
N_NIMCALL(NimStringDesc*, Shortendir_41197)(NimStringDesc* Dir_41199) {
NimStringDesc* Result_41200;
NimStringDesc* Prefix_41205;
NimStringDesc* LOC1;
NimStringDesc* LOC2;
NIM_BOOL LOC4;
NimStringDesc* LOC7;
NimStringDesc* LOC8;
NIM_BOOL LOC10;
NimStringDesc* LOC13;
NIM_BOOL LOC15;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "shortenDir";
F.prev = framePtr;
F.filename = "rod/options.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_41200 = 0;
Prefix_41205 = 0;
F.line = 133;F.filename = "options.nim";
LOC1 = 0;
LOC2 = 0;
LOC2 = Getprefixdir_41106();
LOC1 = rawNewString(LOC2->Sup.len + 1);
appendString(LOC1, LOC2);
appendChar(LOC1, 92);
Prefix_41205 = LOC1;
F.line = 134;F.filename = "options.nim";
LOC4 = nsuStartsWith(Dir_41199, Prefix_41205);
if (!LOC4) goto LA5;
F.line = 135;F.filename = "options.nim";
F.line = 135;F.filename = "options.nim";
Result_41200 = copyStr(Dir_41199, Prefix_41205->Sup.len);
goto BeforeRet;
LA5: ;
F.line = 136;F.filename = "options.nim";
LOC7 = 0;
LOC8 = 0;
LOC8 = nosgetCurrentDir();
LOC7 = rawNewString(LOC8->Sup.len + 1);
appendString(LOC7, LOC8);
appendChar(LOC7, 92);
Prefix_41205 = LOC7;
F.line = 137;F.filename = "options.nim";
LOC10 = nsuStartsWith(Dir_41199, Prefix_41205);
if (!LOC10) goto LA11;
F.line = 138;F.filename = "options.nim";
F.line = 138;F.filename = "options.nim";
Result_41200 = copyStr(Dir_41199, Prefix_41205->Sup.len);
goto BeforeRet;
LA11: ;
F.line = 139;F.filename = "options.nim";
LOC13 = 0;
LOC13 = rawNewString(Projectpath_41110->Sup.len + 1);
appendString(LOC13, Projectpath_41110);
appendChar(LOC13, 92);
Prefix_41205 = LOC13;
F.line = 141;F.filename = "options.nim";
LOC15 = nsuStartsWith(Dir_41199, Prefix_41205);
if (!LOC15) goto LA16;
F.line = 142;F.filename = "options.nim";
F.line = 142;F.filename = "options.nim";
Result_41200 = copyStr(Dir_41199, Prefix_41205->Sup.len);
goto BeforeRet;
LA16: ;
F.line = 143;F.filename = "options.nim";
Result_41200 = copyString(Dir_41199);
BeforeRet: ;
framePtr = framePtr->prev;
return Result_41200;
}
static N_INLINE(NI, subInt)(NI A_6003, NI B_6004) {
NI Result_6005;
NIM_BOOL LOC2;
Result_6005 = 0;
Result_6005 = (NI32)((NU32)(A_6003) - (NU32)(B_6004));
LOC2 = (0 <= (NI32)(Result_6005 ^ A_6003));
if (LOC2) goto LA3;
LOC2 = (0 <= (NI32)(Result_6005 ^ (NI32)((NU32) ~(B_6004))));
LA3: ;
if (!LOC2) goto LA4;
goto BeforeRet;
LA4: ;
raiseOverflow();
BeforeRet: ;
return Result_6005;
}
N_NIMCALL(NimStringDesc*, Removetrailingdirsep_41221)(NimStringDesc* Path_41223) {
NimStringDesc* Result_41224;
NIM_BOOL LOC2;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "removeTrailingDirSep";
F.prev = framePtr;
F.filename = "rod/options.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_41224 = 0;
F.line = 146;F.filename = "options.nim";
LOC2 = (0 < Path_41223->Sup.len);
if (!(LOC2)) goto LA3;
if ((NU)(subInt(Path_41223->Sup.len, 1)) > (NU)(Path_41223->Sup.len)) raiseIndexError();
LOC2 = ((NU8)(Path_41223->data[subInt(Path_41223->Sup.len, 1)]) == (NU8)(92));
LA3: ;
if (!LOC2) goto LA4;
F.line = 147;F.filename = "options.nim";
Result_41224 = copyStrLast(Path_41223, 0, subInt(Path_41223->Sup.len, 2));
goto LA1;
LA4: ;
F.line = 149;F.filename = "options.nim";
Result_41224 = copyString(Path_41223);
LA1: ;
framePtr = framePtr->prev;
return Result_41224;
}
N_NIMCALL(NimStringDesc*, Togeneratedfile_41102)(NimStringDesc* Path_41104, NimStringDesc* Ext_41105) {
NimStringDesc* Result_41239;
TY33378 LOC1;
NimStringDesc* Head_41240;
NimStringDesc* Tail_41241;
NimStringDesc* LOC5;
TY41252 LOC6;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "toGeneratedFile";
F.prev = framePtr;
F.filename = "rod/options.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_41239 = 0;
F.line = 152;F.filename = "options.nim";
memset((void*)&LOC1, 0, sizeof(LOC1));
nosSplitPath(Path_41104, &LOC1);
Head_41240 = 0;
Head_41240 = copyString(LOC1.Head);
Tail_41241 = 0;
Tail_41241 = copyString(LOC1.Tail);
F.line = 153;F.filename = "options.nim";
if (!(0 < Head_41240->Sup.len)) goto LA3;
F.line = 153;F.filename = "options.nim";
LOC5 = 0;
LOC5 = rawNewString(Head_41240->Sup.len + 1);
appendString(LOC5, Head_41240);
appendChar(LOC5, 92);
Head_41240 = Shortendir_41197(LOC5);
LA3: ;
F.line = 154;F.filename = "options.nim";
memset((void*)&LOC6, 0, sizeof(LOC6));
LOC6[0] = copyString(Projectpath_41110);
LOC6[1] = copyString(((NimStringDesc*) &TMP41254));
LOC6[2] = copyString(Head_41240);
LOC6[3] = nosChangeFileExt(Tail_41241, Ext_41105);
Result_41239 = nosJoinPathOpenArray(LOC6, 4);
framePtr = framePtr->prev;
return Result_41239;
}
static N_INLINE(void, pushSafePoint)(TSafePoint* S_4635) {
(*S_4635).prev = excHandler;
excHandler = S_4635;
}
static N_INLINE(void, popSafePoint)(void) {
excHandler = (*excHandler).prev;
}
static N_INLINE(E_Base*, getCurrentException)(void) {
E_Base* Result_19204;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "getCurrentException";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_19204 = 0;
F.line = 1584;F.filename = "system.nim";
Result_19204 = Currexception_4632;
framePtr = framePtr->prev;
return Result_19204;
}
static N_INLINE(NIM_BOOL, Canbecycleroot_11040)(TY10602* C_11042) {
NIM_BOOL Result_11043;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "canbeCycleRoot";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/gc.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_11043 = 0;
F.line = 103;F.filename = "gc.nim";
Result_11043 = !((((*(*C_11042).Typ).flags &(1<<((((NU8) 1))&7)))!=0));
framePtr = framePtr->prev;
return Result_11043;
}
static N_INLINE(void, Rtladdcycleroot_11652)(TY10602* C_11654) {
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "rtlAddCycleRoot";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/gc.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 205;F.filename = "gc.nim";
if (!NIM_TRUE) goto LA2;
F.line = 205;F.filename = "gc.nim";
Dl_8015(&Gch_11010.Cyclerootslock);
LA2: ;
F.line = 206;F.filename = "gc.nim";
Incl_10874(&Gch_11010.Cycleroots, C_11654);
F.line = 207;F.filename = "gc.nim";
if (!NIM_TRUE) goto LA5;
F.line = 207;F.filename = "gc.nim";
Dl_8019(&Gch_11010.Cyclerootslock);
LA5: ;
framePtr = framePtr->prev;
}
static N_INLINE(void, Incref_11802)(TY10602* C_11804) {
NI LOC1;
NIM_BOOL LOC3;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "incRef";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/gc.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 226;F.filename = "gc.nim";
LOC1 = Atomicinc_3001(&(*C_11804).Refcount, 8);
F.line = 227;F.filename = "gc.nim";
LOC3 = Canbecycleroot_11040(C_11804);
if (!LOC3) goto LA4;
F.line = 228;F.filename = "gc.nim";
Rtladdcycleroot_11652(C_11804);
LA4: ;
framePtr = framePtr->prev;
}
static N_INLINE(void, Decref_11664)(TY10602* C_11666) {
NI LOC2;
NIM_BOOL LOC5;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "decRef";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/gc.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 219;F.filename = "gc.nim";
F.line = 220;F.filename = "gc.nim";
LOC2 = Atomicdec_3006(&(*C_11666).Refcount, 8);
if (!((NU32)(LOC2) < (NU32)(8))) goto LA3;
F.line = 221;F.filename = "gc.nim";
Rtladdzct_11658(C_11666);
goto LA1;
LA3: ;
LOC5 = Canbecycleroot_11040(C_11666);
if (!LOC5) goto LA6;
F.line = 223;F.filename = "gc.nim";
Rtladdcycleroot_11652(C_11666);
goto LA1;
LA6: ;
LA1: ;
framePtr = framePtr->prev;
}
static N_INLINE(void, asgnRef)(void** Dest_11814, void* Src_11815) {
TY10602* LOC4;
TY10602* LOC8;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "asgnRef";
F.prev = framePtr;
F.filename = "/home/andreas/projects/nimrod/lib/system/gc.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 235;F.filename = "gc.nim";
F.line = 237;F.filename = "gc.nim";
if (!!((Src_11815 == NIM_NIL))) goto LA2;
F.line = 237;F.filename = "gc.nim";
LOC4 = Usrtocell_11036(Src_11815);
Incref_11802(LOC4);
LA2: ;
F.line = 238;F.filename = "gc.nim";
if (!!(((*Dest_11814) == NIM_NIL))) goto LA6;
F.line = 238;F.filename = "gc.nim";
LOC8 = Usrtocell_11036((*Dest_11814));
Decref_11664(LOC8);
LA6: ;
F.line = 239;F.filename = "gc.nim";
(*Dest_11814) = Src_11815;
framePtr = framePtr->prev;
}
static N_INLINE(void, popCurrentException)(void) {
asgnRef((void**) &Currexception_4632, (*Currexception_4632).parent);
}
N_NIMCALL(NimStringDesc*, Completegeneratedfilepath_41098)(NimStringDesc* F_41100, NIM_BOOL Createsubdir_41101) {
NimStringDesc* Result_41259;
TY33378 LOC1;
NimStringDesc* Head_41260;
NimStringDesc* Tail_41261;
NimStringDesc* LOC5;
NimStringDesc* LOC6;
NimStringDesc* Subdir_41274;
TY41272 LOC7;
TSafePoint TMP41291;
NimStringDesc* LOC11;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "completeGeneratedFilePath";
F.prev = framePtr;
F.filename = "rod/options.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_41259 = 0;
F.line = 157;F.filename = "options.nim";
memset((void*)&LOC1, 0, sizeof(LOC1));
nosSplitPath(F_41100, &LOC1);
Head_41260 = 0;
Head_41260 = copyString(LOC1.Head);
Tail_41261 = 0;
Tail_41261 = copyString(LOC1.Tail);
F.line = 158;F.filename = "options.nim";
if (!(0 < Head_41260->Sup.len)) goto LA3;
F.line = 158;F.filename = "options.nim";
LOC5 = 0;
LOC5 = rawNewString(Head_41260->Sup.len + 1);
appendString(LOC5, Head_41260);
appendChar(LOC5, 92);
LOC6 = 0;
LOC6 = Shortendir_41197(LOC5);
Head_41260 = Removetrailingdirsep_41221(LOC6);
LA3: ;
Subdir_41274 = 0;
F.line = 159;F.filename = "options.nim";
memset((void*)&LOC7, 0, sizeof(LOC7));
LOC7[0] = copyString(Projectpath_41110);
LOC7[1] = copyString(((NimStringDesc*) &TMP41254));
LOC7[2] = copyString(Head_41260);
Subdir_41274 = nosJoinPathOpenArray(LOC7, 3);
F.line = 160;F.filename = "options.nim";
if (!Createsubdir_41101) goto LA9;
F.line = 161;F.filename = "options.nim";
pushSafePoint(&TMP41291);
TMP41291.status = setjmp(TMP41291.context);
framePtr = (TFrame*)&F;
if (TMP41291.status == 0) {
F.line = 162;F.filename = "options.nim";
noscreateDir(Subdir_41274);
popSafePoint();
} else {
popSafePoint();
if (getCurrentException()->Sup.m_type == NTI422) {
F.line = 164;F.filename = "options.nim";
LOC11 = 0;
LOC11 = rawNewString(Subdir_41274->Sup.len + 25);
appendString(LOC11, ((NimStringDesc*) &TMP41292));
appendString(LOC11, Subdir_41274);
Writeln_41286(stdout, LOC11);
F.line = 165;F.filename = "options.nim";
exit(1);
TMP41291.status = 0;popCurrentException();}
}
if (TMP41291.status != 0) reraiseException();
LA9: ;
F.line = 166;F.filename = "options.nim";
Result_41259 = nosJoinPath(Subdir_41274, Tail_41261);
framePtr = framePtr->prev;
return Result_41259;
}
N_NIMCALL(NimStringDesc*, Rawfindfile_41293)(NimStringDesc* F_41295) {
NimStringDesc* Result_41296;
NIM_BOOL LOC2;
TY38015* It_41297;
NIM_BOOL LOC7;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "rawFindFile";
F.prev = framePtr;
F.filename = "rod/options.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_41296 = 0;
F.line = 169;F.filename = "options.nim";
LOC2 = nosexistsFile(F_41295);
if (!LOC2) goto LA3;
F.line = 170;F.filename = "options.nim";
Result_41296 = copyString(F_41295);
goto LA1;
LA3: ;
It_41297 = 0;
F.line = 172;F.filename = "options.nim";
if (Searchpaths_41079.Head) chckObj((*Searchpaths_41079.Head).Sup.m_type, NTI38015);
It_41297 = ((TY38015*) (Searchpaths_41079.Head));
F.line = 173;F.filename = "options.nim";
while (1) {
if (!!((It_41297 == NIM_NIL))) goto LA5;
F.line = 174;F.filename = "options.nim";
Result_41296 = nosJoinPath((*It_41297).Data, F_41295);
F.line = 175;F.filename = "options.nim";
LOC7 = nosexistsFile(Result_41296);
if (!LOC7) goto LA8;
F.line = 175;F.filename = "options.nim";
goto BeforeRet;
LA8: ;
F.line = 176;F.filename = "options.nim";
if ((*It_41297).Sup.Next) chckObj((*(*It_41297).Sup.Next).Sup.m_type, NTI38015);
It_41297 = ((TY38015*) ((*It_41297).Sup.Next));
} LA5: ;
F.line = 177;F.filename = "options.nim";
Result_41296 = copyString(((NimStringDesc*) &TMP41086));
LA1: ;
BeforeRet: ;
framePtr = framePtr->prev;
return Result_41296;
}
N_NIMCALL(NimStringDesc*, Findfile_41087)(NimStringDesc* F_41089) {
NimStringDesc* Result_41313;
NimStringDesc* LOC4;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "FindFile";
F.prev = framePtr;
F.filename = "rod/options.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_41313 = 0;
F.line = 180;F.filename = "options.nim";
Result_41313 = Rawfindfile_41293(F_41089);
F.line = 181;F.filename = "options.nim";
if (!(Result_41313->Sup.len == 0)) goto LA2;
F.line = 181;F.filename = "options.nim";
LOC4 = 0;
LOC4 = nsuToLowerStr(F_41089);
Result_41313 = Rawfindfile_41293(LOC4);
LA2: ;
framePtr = framePtr->prev;
return Result_41313;
}
static N_INLINE(NI, divInt)(NI A_6403, NI B_6404) {
NI Result_6405;
NIM_BOOL LOC5;
Result_6405 = 0;
if (!(B_6404 == 0)) goto LA2;
raiseDivByZero();
LA2: ;
LOC5 = (A_6403 == (-2147483647 -1));
if (!(LOC5)) goto LA6;
LOC5 = (B_6404 == -1);
LA6: ;
if (!LOC5) goto LA7;
raiseOverflow();
LA7: ;
Result_6405 = (NI32)(A_6403 / B_6404);
goto BeforeRet;
BeforeRet: ;
return Result_6405;
}
N_NIMCALL(NI, Binarystrsearch_41146)(NimStringDesc** X_41149, NI X_41149Len0, NimStringDesc* Y_41150) {
NI Result_41323;
NI A_41324;
NI B_41335;
NI Mid_41338;
NI C_41339;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "binaryStrSearch";
F.prev = framePtr;
F.filename = "rod/options.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
Result_41323 = 0;
A_41324 = 0;
F.line = 184;F.filename = "options.nim";
A_41324 = 0;
B_41335 = 0;
F.line = 185;F.filename = "options.nim";
B_41335 = subInt(X_41149Len0, 1);
F.line = 186;F.filename = "options.nim";
while (1) {
if (!(A_41324 <= B_41335)) goto LA1;
Mid_41338 = 0;
F.line = 187;F.filename = "options.nim";
Mid_41338 = divInt(addInt(A_41324, B_41335), 2);
C_41339 = 0;
F.line = 188;F.filename = "options.nim";
if ((NU)(Mid_41338) >= (NU)(X_41149Len0)) raiseIndexError();
C_41339 = nsuCmpIgnoreCase(X_41149[Mid_41338], Y_41150);
F.line = 189;F.filename = "options.nim";
if (!(C_41339 < 0)) goto LA3;
F.line = 190;F.filename = "options.nim";
A_41324 = addInt(Mid_41338, 1);
goto LA2;
LA3: ;
if (!(0 < C_41339)) goto LA5;
F.line = 192;F.filename = "options.nim";
B_41335 = subInt(Mid_41338, 1);
goto LA2;
LA5: ;
F.line = 194;F.filename = "options.nim";
F.line = 194;F.filename = "options.nim";
Result_41323 = Mid_41338;
goto BeforeRet;
LA2: ;
} LA1: ;
F.line = 195;F.filename = "options.nim";
Result_41323 = -1;
BeforeRet: ;
framePtr = framePtr->prev;
return Result_41323;
}
N_NIMCALL(void, Writeln_41286)(FILE* F_41289, NimStringDesc* X_41290) {
Write_3658(F_41289, X_41290);
Write_3658(F_41289, ((NimStringDesc*) &TMP41353));
}
N_NOINLINE(void, optionsInit)(void) {
TY41352 LOC1;
volatile struct {TFrame* prev;NCSTRING procname;NI line;NCSTRING filename;NI len;
} F;
F.procname = "options";
F.prev = framePtr;
F.filename = "rod/options.nim";
F.line = 0;
framePtr = (TFrame*)&F;
F.len = 0;
F.line = 63;F.filename = "options.nim";
Goptions_41075 = 105022;
F.line = 66;F.filename = "options.nim";
Gglobaloptions_41077 = 8;
Searchpaths_41079.m_type = NTI38019;
F.line = 69;F.filename = "options.nim";
asgnRefNoCycle((void**) &Outfile_41080, copyString(((NimStringDesc*) &TMP41086)));
F.line = 70;F.filename = "options.nim";
asgnRefNoCycle((void**) &Gindexfile_41081, copyString(((NimStringDesc*) &TMP41086)));
F.line = 71;F.filename = "options.nim";
Gcmd_41082 = ((NU8) 0);
F.line = 96;F.filename = "options.nim";
asgnRefNoCycle((void**) &Libpath_41109, copyString(((NimStringDesc*) &TMP41086)));
F.line = 97;F.filename = "options.nim";
asgnRefNoCycle((void**) &Projectpath_41110, copyString(((NimStringDesc*) &TMP41086)));
F.line = 98;F.filename = "options.nim";
Gkeepcomments_41111 = NIM_TRUE;
F.line = 99;F.filename = "options.nim";
asgnRefNoCycle((void**) &Gimplicitmods_41128, (TY4377*) newSeq(NTI4377, 0));
F.line = 197;F.filename = "options.nim";
memset((void*)&LOC1, 0, sizeof(LOC1));
asgnRefNoCycle((void**) &Gconfigvars_41108, Newstringtable_40019(LOC1, 0, ((NU8) 2)));
framePtr = framePtr->prev;
}


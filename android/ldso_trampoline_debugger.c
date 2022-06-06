/*
 * Copyright (C) 2021 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// Normally gdb and lldb look for a symbol named "_dl_debug_state" in the
// interpreter to get notified when the dynamic loader has modified the
// list of shared libraries.  When using the embeded linker, the debugger is not
// aware of the interpreter (PT_INTERP is unset and auxv AT_BASE is 0) so it
// doesn't know where to look for the symbol.  It falls back to looking in the
// executable, so provide a symbol for it to find.  The dynamic loader will
// need to forward its calls to its own _dl_debug_state symbol to this one.
//
// This has to be defined in a .c file because lldb looks for a symbol with
// DWARF language type DW_LANG_C.
extern void _dl_debug_state() {
}

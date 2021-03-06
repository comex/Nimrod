
#
#  $Id: sdl_ttf.pas,v 1.18 2007/06/01 11:16:33 savage Exp $
#
#
#******************************************************************************
#                                                                              
#          JEDI-SDL : Pascal units for SDL - Simple DirectMedia Layer          
#       Conversion of the Simple DirectMedia Layer Headers                     
#                                                                              
# Portions created by Sam Lantinga <slouken@devolution.com> are                
# Copyright (C) 1997, 1998, 1999, 2000, 2001  Sam Lantinga                     
# 5635-34 Springhouse Dr.                                                      
# Pleasanton, CA 94588 (USA)                                                   
#                                                                              
# All Rights Reserved.                                                         
#                                                                              
# The original files are : SDL_ttf.h                                           
#                                                                              
# The initial developer of this Pascal code was :                              
# Dominqiue Louis <Dominique@SavageSoftware.com.au>                            
#                                                                              
# Portions created by Dominqiue Louis are                                      
# Copyright (C) 2000 - 2001 Dominqiue Louis.                                   
#                                                                              
#                                                                              
# Contributor(s)                                                               
# --------------                                                               
# Tom Jones <tigertomjones@gmx.de>  His Project inspired this conversion       
#                                                                              
# Obtained through:                                                            
# Joint Endeavour of Delphi Innovators ( Project JEDI )                        
#                                                                              
# You may retrieve the latest version of this file at the Project              
# JEDI home page, located at http://delphi-jedi.org                            
#                                                                              
# The contents of this file are used with permission, subject to               
# the Mozilla Public License Version 1.1 (the "License"); you may              
# not use this file except in compliance with the License. You may             
# obtain a copy of the License at                                              
# http://www.mozilla.org/MPL/MPL-1.1.html                                      
#                                                                              
# Software distributed under the License is distributed on an                  
# "AS IS" basis, WITHOUT WARRANTY OF ANY KIND, either express or               
# implied. See the License for the specific language governing                 
# rights and limitations under the License.                                    
#                                                                              
# Description                                                                  
# -----------                                                                  
#                                                                              
#                                                                              
#                                                                              
#                                                                              
#                                                                              
#                                                                              
#                                                                              
# Requires                                                                     
# --------                                                                     
#   The SDL Runtime libraris on Win32  : SDL.dll on Linux : libSDL.so          
#   They are available from...                                                 
#   http://www.libsdl.org .                                                    
#                                                                              
# Programming Notes                                                            
# -----------------                                                            
#                                                                              
#                                                                              
#                                                                              
#                                                                              
# Revision History                                                             
# ----------------                                                             
#   December 08 2002 - DL : Fixed definition of TTF_RenderUnicode_Solid        
#                                                                              
#   April   03 2003 - DL : Added jedi-sdl.inc include file to support more     
#                          Pascal compilers. Initial support is now included   
#                          for GnuPascal, VirtualPascal, TMT and obviously     
#                          continue support for Delphi Kylix and FreePascal.   
#                                                                              
#   April   24 2003 - DL : under instruction from Alexey Barkovoy, I have added
#                          better TMT Pascal support and under instruction     
#                          from Prof. Abimbola Olowofoyeku (The African Chief),
#                          I have added better Gnu Pascal support              
#                                                                              
#   April   30 2003 - DL : under instruction from David Mears AKA              
#                          Jason Siletto, I have added FPC Linux support.      
#                          This was compiled with fpc 1.1, so remember to set  
#                          include file path. ie. -Fi/usr/share/fpcsrc/rtl/*   
#                                                                              
#
#  $Log: sdl_ttf.pas,v $
#  Revision 1.18  2007/06/01 11:16:33  savage
#  Added IFDEF UNIX for Workaround.
#
#  Revision 1.17  2007/06/01 08:38:21  savage
#  Added TTF_RenderText_Solid workaround as suggested by Michalis Kamburelis
#
#  Revision 1.16  2007/05/29 21:32:14  savage
#  Changes as suggested by Almindor for 64bit compatibility.
#
#  Revision 1.15  2007/05/20 20:32:45  savage
#  Initial Changes to Handle 64 Bits
#
#  Revision 1.14  2006/12/02 00:19:01  savage
#  Updated to latest version
#
#  Revision 1.13  2005/04/10 11:48:33  savage
#  Changes as suggested by Michalis, thanks.
#
#  Revision 1.12  2005/01/05 01:47:14  savage
#  Changed LibName to reflect what MacOS X should have. ie libSDL*-1.2.0.dylib respectively.
#
#  Revision 1.11  2005/01/04 23:14:57  savage
#  Changed LibName to reflect what most Linux distros will have. ie libSDL*-1.2.so.0 respectively.
#
#  Revision 1.10  2005/01/02 19:07:32  savage
#  Slight bug fix to use LongInt instead of Long ( Thanks Michalis Kamburelis )
#
#  Revision 1.9  2005/01/01 02:15:20  savage
#  Updated to v2.0.7
#
#  Revision 1.8  2004/10/07 21:02:32  savage
#  Fix for FPC
#
#  Revision 1.7  2004/09/30 22:39:50  savage
#  Added a true type font class which contains a wrap text function.
#  Changed the sdl_ttf.pas header to reflect the future of jedi-sdl.
#
#  Revision 1.6  2004/08/14 22:54:30  savage
#  Updated so that Library name defines are correctly defined for MacOS X.
#
#  Revision 1.5  2004/05/10 14:10:04  savage
#  Initial MacOS X support. Fixed defines for MACOS ( Classic ) and DARWIN ( MacOS X ).
#
#  Revision 1.4  2004/04/13 09:32:08  savage
#  Changed Shared object names back to just the .so extension to avoid conflicts on various Linux/Unix distros. Therefore developers will need to create Symbolic links to the actual Share Objects if necessary.
#
#  Revision 1.3  2004/04/01 20:53:24  savage
#  Changed Linux Shared Object names so they reflect the Symbolic Links that are created when installing the RPMs from the SDL site.
#
#  Revision 1.2  2004/03/30 20:23:28  savage
#  Tidied up use of UNIX compiler directive.
#
#  Revision 1.1  2004/02/16 22:16:40  savage
#  v1.0 changes
#
#  
#
#******************************************************************************
#
#  Define this to workaround a known bug in some freetype versions.
#  The error manifests as TTF_RenderGlyph_Solid returning nil (error)
#  and error message (in SDL_Error) is
#  "Failed loading DPMSDisable: /usr/lib/libX11.so.6: undefined symbol: DPMSDisable"
#  See [http://lists.libsdl.org/pipermail/sdl-libsdl.org/2007-March/060459.html]
#

import sdl

when defined(windows):
  const SDLttfLibName = "SDL_ttf.dll"
elif defined(macosx):
  const SDLttfLibName = "libSDL_ttf-2.0.0.dylib"
else:
  const SDLttfLibName = "libSDL_ttf.so"

const
  SDL_TTF_MAJOR_VERSION* = 2'i8
  SDL_TTF_MINOR_VERSION* = 0'i8
  SDL_TTF_PATCHLEVEL* = 8'i8     # Backwards compatibility
  TTF_MAJOR_VERSION* = SDL_TTF_MAJOR_VERSION
  TTF_MINOR_VERSION* = SDL_TTF_MINOR_VERSION
  TTF_PATCHLEVEL* = SDL_TTF_PATCHLEVEL #*
                                       #   Set and retrieve the font style
                                       #   This font style is implemented by modifying the font glyphs, and
                                       #   doesn't reflect any inherent properties of the truetype font file.
                                       #*
  TTF_STYLE_NORMAL* = 0x00000000
  TTF_STYLE_BOLD* = 0x00000001
  TTF_STYLE_ITALIC* = 0x00000002
  TTF_STYLE_UNDERLINE* = 0x00000004 # ZERO WIDTH NO-BREAKSPACE (Unicode byte order mark)
  UNICODE_BOM_NATIVE* = 0x0000FEFF
  UNICODE_BOM_SWAPPED* = 0x0000FFFE

type 
  PTTF_Font* = ptr TTTF_font
  TTTF_Font*{.final.} = object  # This macro can be used to fill a version structure with the compile-time
                                #  version of the SDL_ttf library. 

proc SDL_TTF_VERSION*(X: var TSDL_version)
  # This function gets the version of the dynamically linked SDL_ttf library.
  #     It should NOT be used to fill a version structure, instead you should use the
  #     SDL_TTF_VERSION() macro. 
proc TTF_Linked_Version*(): PSDL_version{.cdecl, importc, dynlib: SDLttfLibName.}
  # This function tells the library whether UNICODE text is generally
  #   byteswapped.  A UNICODE BOM character in a string will override
  #   this setting for the remainder of that string.
  #
proc TTF_ByteSwappedUNICODE*(swapped: int){.cdecl, importc, dynlib: SDLttfLibName.}
  #returns 0 on succes, -1 if error occurs
proc TTF_Init*(): int{.cdecl, importc, dynlib: SDLttfLibName.}
  #
  # Open a font file and create a font of the specified point size.
  # Some .fon fonts will have several sizes embedded in the file, so the
  # point size becomes the index of choosing which size.  If the value
  # is too high, the last indexed size will be the default.
  #
proc TTF_OpenFont*(filename: cstring, ptsize: int): PTTF_Font{.cdecl, 
    importc, dynlib: SDLttfLibName.}
proc TTF_OpenFontIndex*(filename: cstring, ptsize: int, index: int32): PTTF_Font{.
    cdecl, importc, dynlib: SDLttfLibName.}
proc TTF_OpenFontRW*(src: PSDL_RWops, freesrc: int, ptsize: int): PTTF_Font{.
    cdecl, importc, dynlib: SDLttfLibName.}
proc TTF_OpenFontIndexRW*(src: PSDL_RWops, freesrc: int, ptsize: int, 
                          index: int32): PTTF_Font{.cdecl, importc, dynlib: SDLttfLibName.}
proc TTF_GetFontStyle*(font: PTTF_Font): int{.cdecl, importc, dynlib: SDLttfLibName.}
proc TTF_SetFontStyle*(font: PTTF_Font, style: int){.cdecl, 
    importc, dynlib: SDLttfLibName.}
  # Get the total height of the font - usually equal to point size 
proc TTF_FontHeight*(font: PTTF_Font): int{.cdecl, importc, dynlib: SDLttfLibName.}
  # Get the offset from the baseline to the top of the font
  #   This is a positive value, relative to the baseline.
  #
proc TTF_FontAscent*(font: PTTF_Font): int{.cdecl, importc, dynlib: SDLttfLibName.}
  # Get the offset from the baseline to the bottom of the font
  #   This is a negative value, relative to the baseline.
  #
proc TTF_FontDescent*(font: PTTF_Font): int{.cdecl, importc, dynlib: SDLttfLibName.}
  # Get the recommended spacing between lines of text for this font 
proc TTF_FontLineSkip*(font: PTTF_Font): int{.cdecl, importc, dynlib: SDLttfLibName.}
  # Get the number of faces of the font 
proc TTF_FontFaces*(font: PTTF_Font): int32{.cdecl, importc, dynlib: SDLttfLibName.}
  # Get the font face attributes, if any 
proc TTF_FontFaceIsFixedWidth*(font: PTTF_Font): int{.cdecl, 
    importc, dynlib: SDLttfLibName.}
proc TTF_FontFaceFamilyName*(font: PTTF_Font): cstring{.cdecl, 
    importc, dynlib: SDLttfLibName.}
proc TTF_FontFaceStyleName*(font: PTTF_Font): cstring{.cdecl, 
    importc, dynlib: SDLttfLibName.}
  # Get the metrics (dimensions) of a glyph 
proc TTF_GlyphMetrics*(font: PTTF_Font, ch: Uint16, minx: var int, 
                       maxx: var int, miny: var int, maxy: var int, 
                       advance: var int): int{.cdecl, importc, dynlib: SDLttfLibName.}
  # Get the dimensions of a rendered string of text 
proc TTF_SizeText*(font: PTTF_Font, text: cstring, w: var int, y: var int): int{.
    cdecl, importc, dynlib: SDLttfLibName.}
proc TTF_SizeUTF8*(font: PTTF_Font, text: cstring, w: var int, y: var int): int{.
    cdecl, importc, dynlib: SDLttfLibName.}
proc TTF_SizeUNICODE*(font: PTTF_Font, text: PUint16, w: var int, y: var int): int{.
    cdecl, importc, dynlib: SDLttfLibName.}
  # Create an 8-bit palettized surface and render the given text at
  #   fast quality with the given font and color.  The 0 pixel is the
  #   colorkey, giving a transparent background, and the 1 pixel is set
  #   to the text color.
  #   This function returns the new surface, or NULL if there was an error.
  #
proc TTF_RenderUTF8_Solid*(font: PTTF_Font, text: cstring, fg: TSDL_Color): PSDL_Surface{.
    cdecl, importc, dynlib: SDLttfLibName.}
proc TTF_RenderUNICODE_Solid*(font: PTTF_Font, text: PUint16, fg: TSDL_Color): PSDL_Surface{.
    cdecl, importc, dynlib: SDLttfLibName.}
  #
  #Create an 8-bit palettized surface and render the given glyph at
  #   fast quality with the given font and color.  The 0 pixel is the
  #   colorkey, giving a transparent background, and the 1 pixel is set
  #   to the text color.  The glyph is rendered without any padding or
  #   centering in the X direction, and aligned normally in the Y direction.
  #   This function returns the new surface, or NULL if there was an error.
  #
proc TTF_RenderGlyph_Solid*(font: PTTF_Font, ch: Uint16, fg: TSDL_Color): PSDL_Surface{.
    cdecl, importc, dynlib: SDLttfLibName.}
  # Create an 8-bit palettized surface and render the given text at
  #   high quality with the given font and colors.  The 0 pixel is background,
  #   while other pixels have varying degrees of the foreground color.
  #   This function returns the new surface, or NULL if there was an error.
  #
proc TTF_RenderText_Shaded*(font: PTTF_Font, text: cstring, fg: TSDL_Color, 
                            bg: TSDL_Color): PSDL_Surface{.cdecl, 
    importc, dynlib: SDLttfLibName.}
proc TTF_RenderUTF8_Shaded*(font: PTTF_Font, text: cstring, fg: TSDL_Color, 
                            bg: TSDL_Color): PSDL_Surface{.cdecl, 
    importc, dynlib: SDLttfLibName.}
proc TTF_RenderUNICODE_Shaded*(font: PTTF_Font, text: PUint16, fg: TSDL_Color, 
                               bg: TSDL_Color): PSDL_Surface{.cdecl, 
    importc, dynlib: SDLttfLibName.}
  # Create an 8-bit palettized surface and render the given glyph at
  #   high quality with the given font and colors.  The 0 pixel is background,
  #   while other pixels have varying degrees of the foreground color.
  #   The glyph is rendered without any padding or centering in the X
  #   direction, and aligned normally in the Y direction.
  #   This function returns the new surface, or NULL if there was an error.
  #
proc TTF_RenderGlyph_Shaded*(font: PTTF_Font, ch: Uint16, fg: TSDL_Color, 
                             bg: TSDL_Color): PSDL_Surface{.cdecl, 
    importc, dynlib: SDLttfLibName.}
  # Create a 32-bit ARGB surface and render the given text at high quality,
  #   using alpha blending to dither the font with the given color.
  #   This function returns the new surface, or NULL if there was an error.
  #
proc TTF_RenderText_Blended*(font: PTTF_Font, text: cstring, fg: TSDL_Color): PSDL_Surface{.
    cdecl, importc, dynlib: SDLttfLibName.}
proc TTF_RenderUTF8_Blended*(font: PTTF_Font, text: cstring, fg: TSDL_Color): PSDL_Surface{.
    cdecl, importc, dynlib: SDLttfLibName.}
proc TTF_RenderUNICODE_Blended*(font: PTTF_Font, text: PUint16, fg: TSDL_Color): PSDL_Surface{.
    cdecl, importc, dynlib: SDLttfLibName.}
  # Create a 32-bit ARGB surface and render the given glyph at high quality,
  #   using alpha blending to dither the font with the given color.
  #   The glyph is rendered without any padding or centering in the X
  #   direction, and aligned normally in the Y direction.
  #   This function returns the new surface, or NULL if there was an error.
  #
proc TTF_RenderGlyph_Blended*(font: PTTF_Font, ch: Uint16, fg: TSDL_Color): PSDL_Surface{.
    cdecl, importc, dynlib: SDLttfLibName.}
  # For compatibility with previous versions, here are the old functions 
  ##define TTF_RenderText(font, text, fg, bg)
  #	TTF_RenderText_Shaded(font, text, fg, bg)
  ##define TTF_RenderUTF8(font, text, fg, bg)	
  #	TTF_RenderUTF8_Shaded(font, text, fg, bg)
  ##define TTF_RenderUNICODE(font, text, fg, bg)	
  #	TTF_RenderUNICODE_Shaded(font, text, fg, bg)
  # Close an opened font file 
proc TTF_CloseFont*(font: PTTF_Font){.cdecl, importc, dynlib: SDLttfLibName.}
  #De-initialize TTF engine
proc TTF_Quit*(){.cdecl, importc, dynlib: SDLttfLibName.}
  # Check if the TTF engine is initialized
proc TTF_WasInit*(): int{.cdecl, importc, dynlib: SDLttfLibName.}
  # We'll use SDL for reporting errors
proc TTF_SetError*(fmt: cstring)
proc TTF_GetError*(): cstring
# implementation

proc SDL_TTF_VERSION(X: var TSDL_version) = 
  X.major = SDL_TTF_MAJOR_VERSION
  X.minor = SDL_TTF_MINOR_VERSION
  X.patch = SDL_TTF_PATCHLEVEL

proc TTF_SetError(fmt: cstring) = 
  SDL_SetError(fmt)

proc TTF_GetError(): cstring = 
  result = SDL_GetError()

when not(defined(Workaround_TTF_RenderText_Solid)): 
  proc TTF_RenderText_Solid*(font: PTTF_Font, text: cstring, fg: TSDL_Color): PSDL_Surface{.
      cdecl, importc, dynlib: SDLttfLibName.}
else: 
  proc TTF_RenderText_Solid(font: PTTF_Font, text: cstring, fg: TSDL_Color): PSDL_Surface = 
    var Black: TSDL_Color # initialized to zero
    Result = TTF_RenderText_Shaded(font, text, fg, Black)

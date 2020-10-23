// ----------------------------------------------------------------------
// Original work Copyright © 2005-2020 Rich Felker, et al.
// Modified work Copyright © 2020 Haddon Chippington Derrick.
//
// Permission is hereby granted, free of charge, to any person obtaining
// a copy of this software and associated documentation files (the
// "Software"), to deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to
// permit persons to whom the Software is furnished to do so, subject to
// the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
// IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
// CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
// TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
// SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
// ----------------------------------------------------------------------
//
// Authors/contributors to the original musl include:
//
// A. Wilcox
// Ada Worcester
// Alex Dowad
// Alex Suykov
// Alexander Monakov
// Andre McCurdy
// Andrew Kelley
// Anthony G. Basile
// Aric Belsito
// Arvid Picciani
// Bartosz Brachaczek
// Benjamin Peterson
// Bobby Bingham
// Boris Brezillon
// Brent Cook
// Chris Spiegel
// Clément Vasseur
// Daniel Micay
// Daniel Sabogal
// Daurnimator
// David Carlier
// David Edelsohn
// Denys Vlasenko
// Dmitry Ivanov
// Dmitry V. Levin
// Drew DeVault
// Emil Renner Berthing
// Fangrui Song
// Felix Fietkau
// Felix Janda
// Gianluca Anzolin
// Hauke Mehrtens
// He X
// Hiltjo Posthuma
// Isaac Dunham
// Jaydeep Patil
// Jens Gustedt
// Jeremy Huntwork
// Jo-Philipp Wich
// Joakim Sindholt
// John Spencer
// Julien Ramseier
// Justin Cormack
// Kaarle Ritvanen
// Khem Raj
// Kylie McClain
// Leah Neukirchen
// Luca Barbato
// Luka Perkov
// M Farkas-Dyck (Strake)
// Mahesh Bodapati
// Markus Wichmann
// Masanori Ogino
// Michael Clark
// Michael Forney
// Mikhail Kremnyov
// Natanael Copa
// Nicholas J. Kain
// orc
// Pascal Cuoq
// Patrick Oppenlander
// Petr Hosek
// Petr Skocik
// Pierre Carrier
// Reini Urban
// Rich Felker
// Richard Pennington
// Ryan Fairfax
// Samuel Holland
// Segev Finer
// Shiz
// sin
// Solar Designer
// Stefan Kristiansson
// Stefan O'Rear
// Szabolcs Nagy
// Timo Teräs
// Trutz Behn
// Valentin Ochs
// Will Dietz
// William Haddon
// William Pitcock
//
// Portions of this software are derived from third-party works licensed
// under terms compatible with the above MIT license:
//
// The TRE regular expression implementation (src/regex/reg* and
// src/regex/tre*) is Copyright © 2001-2008 Ville Laurikari and licensed
// under a 2-clause BSD license (license text in the source files). The
// included version has been heavily modified by Rich Felker in 2012, in
// the interests of size, simplicity, and namespace cleanliness.
//
// Much of the math library code (src/math/* and src/complex/*) is
// Copyright © 1993,2004 Sun Microsystems or
// Copyright © 2003-2011 David Schultz or
// Copyright © 2003-2009 Steven G. Kargl or
// Copyright © 2003-2009 Bruce D. Evans or
// Copyright © 2008 Stephen L. Moshier or
// Copyright © 2017-2018 Arm Limited
// and labelled as such in comments in the individual source files. All
// have been licensed under extremely permissive terms.
//
// The ARM memcpy code (src/string/arm/memcpy.S) is Copyright © 2008
// The Android Open Source Project and is licensed under a two-clause BSD
// license. It was taken from Bionic libc, used on Android.
//
// The AArch64 memcpy and memset code (src/string/aarch64/*) are
// Copyright © 1999-2019, Arm Limited.
//
// The implementation of DES for crypt (src/crypt/crypt_des.c) is
// Copyright © 1994 David Burren. It is licensed under a BSD license.
//
// The implementation of blowfish crypt (src/crypt/crypt_blowfish.c) was
// originally written by Solar Designer and placed into the public
// domain. The code also comes with a fallback permissive license for use
// in jurisdictions that may not recognize the public domain.
//
// The smoothsort implementation (src/stdlib/qsort.c) is Copyright © 2011
// Valentin Ochs and is licensed under an MIT-style license.
//
// The x86_64 port was written by Nicholas J. Kain and is licensed under
// the standard MIT terms.
//
// The mips and microblaze ports were originally written by Richard
// Pennington for use in the ellcc project. The original code was adapted
// by Rich Felker for build system and code conventions during upstream
// integration. It is licensed under the standard MIT terms.
//
// The mips64 port was contributed by Imagination Technologies and is
// licensed under the standard MIT terms.
//
// The powerpc port was also originally written by Richard Pennington,
// and later supplemented and integrated by John Spencer. It is licensed
// under the standard MIT terms.
//
// All other files which have no copyright comments are original works
// produced specifically for use as part of this library, written either
// by Rich Felker, the main author of the library, or by one or more
// contibutors listed above. Details on authorship of individual files
// can be found in the git version control history of the project. The
// omission of copyright and license comments in each file is in the
// interest of source tree size.
//
// In addition, permission is hereby granted for all public header files
// (include/* and arch/*/bits/*) and crt files intended to be linked into
// applications (crt/*, ldso/dlstart.c, and arch/*/crt_arch.h) to omit
// the copyright notice and permission notice otherwise required by the
// license, and to use these files without any requirement of
// attribution. These files include substantial contributions from:
//
// Bobby Bingham
// John Spencer
// Nicholas J. Kain
// Rich Felker
// Richard Pennington
// Stefan Kristiansson
// Szabolcs Nagy
//
// all of whom have explicitly granted such permission.
//
// This file previously contained text expressing a belief that most of
// the files covered by the above exception were sufficiently trivial not
// to be subject to copyright, resulting in confusion over whether it
// negated the permissions granted in the license. In the spirit of
// permissive licensing, and of not having licensing issues being an
// obstacle to adoption, that text has been removed.
//

#ifndef MR_MUSL_HPP_
#define MR_MUSL_HPP_

namespace mr_musl
{
  namespace math
  {
    double sin(double x);
  }
}

#endif // MR_MUSL_HPP_

#ifdef MR_MUSL_IMPLEMENTATION

typedef signed int int32_t;
static_assert(sizeof(int32_t) == 4, "assuming int32_t is signed int");

typedef unsigned int uint32_t;
static_assert(sizeof(uint32_t) == 4, "assuming uint32_t is unsigned int");

typedef unsigned long long uint64_t;
static_assert(sizeof(uint64_t) == 8, "assuming uint64_t is unsigned long long");

typedef double double_t;
static_assert(sizeof(double_t) == 8, "assuming double_t is double");

#define DBL_EPSILON 2.22044604925031308085e-16

#if FLT_EVAL_METHOD==0 || FLT_EVAL_METHOD==1
#define EPS DBL_EPSILON
#elif FLT_EVAL_METHOD==2
#define EPS LDBL_EPSILON
#endif

// musl file begin: src/internal/libm.h
/* Helps static branch prediction so hot path can be better optimized.  */
#ifdef __GNUC__
#define predict_true(x) __builtin_expect(!!(x), 1)
#define predict_false(x) __builtin_expect(x, 0)
#else
#define predict_true(x) (x)
#define predict_false(x) (x)
#endif

static inline void fp_force_evalf(float x)
{
  volatile float y;
  y = x;
}

static inline void fp_force_eval(double x)
{
  volatile double y;
  y = x;
}

static inline void fp_force_evall(long double x)
{
  volatile long double y;
  y = x;
}

#define FORCE_EVAL(x) do {                        \
  if (sizeof(x) == sizeof(float)) {         \
    fp_force_evalf(x);                \
  } else if (sizeof(x) == sizeof(double)) { \
    fp_force_eval(x);                 \
  } else {                                  \
    fp_force_evall(x);                \
  }                                         \
} while(0)

union asuint64_helper
{
  double _f;
  uint64_t _i;
};

#define asuint64(f) ((asuint64_helper){f})._i

#define GET_HIGH_WORD(hi,d)                       \
do {                                              \
  (hi) = asuint64(d) >> 32;                       \
} while (0)
// musl file end: src/internal/libm.h

// musl file begin: src/math/floor.c
double floor(double x)
{
  static const double_t toint = 1/EPS;

  union {double f; uint64_t i;} u = {x};
  int e = u.i >> 52 & 0x7ff;
  double_t y;

  if (e >= 0x3ff+52 || x == 0)
    return x;
  /* y = int(x) - x, where int(x) is an integer neighbor of x */
  if (u.i >> 63)
    y = x - toint + toint - x;
  else
    y = x + toint - toint - x;
  /* special case because of non-nearest rounding modes */
  if (e <= 0x3ff-1) {
    FORCE_EVAL(y);
    return u.i >> 63 ? -1 : 0;
  }
  if (y > 0)
    return x + y - 1;
  return x + y;
}
// musl file end: src/math/floor.c

// musl file begin: src/math/scalbn.c
double scalbn(double x, int n)
{
  union {double f; uint64_t i;} u;
  double_t y = x;

  if (n > 1023) {
    y *= 0x1p1023;
    n -= 1023;
    if (n > 1023) {
      y *= 0x1p1023;
      n -= 1023;
      if (n > 1023)
        n = 1023;
    }
  } else if (n < -1022) {
    /* make sure final n < -53 to avoid double
       rounding in the subnormal range */
    y *= 0x1p-1022 * 0x1p53;
    n += 1022 - 53;
    if (n < -1022) {
      y *= 0x1p-1022 * 0x1p53;
      n += 1022 - 53;
      if (n < -1022)
        n = -1022;
    }
  }
  u.i = (uint64_t)(0x3ff+n)<<52;
  x = y * u.f;
  return x;
}
// musl file end: src/math/scalbn.c

// musl file begin: src/math/__rem_pio2_large.c
/* origin: FreeBSD /usr/src/lib/msun/src/k_rem_pio2.c */
/*
 * ====================================================
 * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
 *
 * Developed at SunSoft, a Sun Microsystems, Inc. business.
 * Permission to use, copy, modify, and distribute this
 * software is freely granted, provided that this notice
 * is preserved.
 * ====================================================
 */
/*
 * __rem_pio2_large(x,y,e0,nx,prec)
 * double x[],y[]; int e0,nx,prec;
 *
 * __rem_pio2_large return the last three digits of N with
 *              y = x - N*pi/2
 * so that |y| < pi/2.
 *
 * The method is to compute the integer (mod 8) and fraction parts of
 * (2/pi)*x without doing the full multiplication. In general we
 * skip the part of the product that are known to be a huge integer (
 * more accurately, = 0 mod 8 ). Thus the number of operations are
 * independent of the exponent of the input.
 *
 * (2/pi) is represented by an array of 24-bit integers in ipio2[].
 *
 * Input parameters:
 *      x[]     The input value (must be positive) is broken into nx
 *              pieces of 24-bit integers in double precision format.
 *              x[i] will be the i-th 24 bit of x. The scaled exponent
 *              of x[0] is given in input parameter e0 (i.e., x[0]*2^e0
 *              match x's up to 24 bits.
 *
 *              Example of breaking a double positive z into x[0]+x[1]+x[2]:
 *                      e0 = ilogb(z)-23
 *                      z  = scalbn(z,-e0)
 *              for i = 0,1,2
 *                      x[i] = floor(z)
 *                      z    = (z-x[i])*2**24
 *
 *
 *      y[]     ouput result in an array of double precision numbers.
 *              The dimension of y[] is:
 *                      24-bit  precision       1
 *                      53-bit  precision       2
 *                      64-bit  precision       2
 *                      113-bit precision       3
 *              The actual value is the sum of them. Thus for 113-bit
 *              precison, one may have to do something like:
 *
 *              long double t,w,r_head, r_tail;
 *              t = (long double)y[2] + (long double)y[1];
 *              w = (long double)y[0];
 *              r_head = t+w;
 *              r_tail = w - (r_head - t);
 *
 *      e0      The exponent of x[0]. Must be <= 16360 or you need to
 *              expand the ipio2 table.
 *
 *      nx      dimension of x[]
 *
 *      prec    an integer indicating the precision:
 *                      0       24  bits (single)
 *                      1       53  bits (double)
 *                      2       64  bits (extended)
 *                      3       113 bits (quad)
 *
 * External function:
 *      double scalbn(), floor();
 *
 *
 * Here is the description of some local variables:
 *
 *      jk      jk+1 is the initial number of terms of ipio2[] needed
 *              in the computation. The minimum and recommended value
 *              for jk is 3,4,4,6 for single, double, extended, and quad.
 *              jk+1 must be 2 larger than you might expect so that our
 *              recomputation test works. (Up to 24 bits in the integer
 *              part (the 24 bits of it that we compute) and 23 bits in
 *              the fraction part may be lost to cancelation before we
 *              recompute.)
 *
 *      jz      local integer variable indicating the number of
 *              terms of ipio2[] used.
 *
 *      jx      nx - 1
 *
 *      jv      index for pointing to the suitable ipio2[] for the
 *              computation. In general, we want
 *                      ( 2^e0*x[0] * ipio2[jv-1]*2^(-24jv) )/8
 *              is an integer. Thus
 *                      e0-3-24*jv >= 0 or (e0-3)/24 >= jv
 *              Hence jv = max(0,(e0-3)/24).
 *
 *      jp      jp+1 is the number of terms in PIo2[] needed, jp = jk.
 *
 *      q[]     double array with integral value, representing the
 *              24-bits chunk of the product of x and 2/pi.
 *
 *      q0      the corresponding exponent of q[0]. Note that the
 *              exponent for q[i] would be q0-24*i.
 *
 *      PIo2[]  double precision array, obtained by cutting pi/2
 *              into 24 bits chunks.
 *
 *      f[]     ipio2[] in floating point
 *
 *      iq[]    integer array by breaking up q[] in 24-bits chunk.
 *
 *      fq[]    final product of x*(2/pi) in fq[0],..,fq[jk]
 *
 *      ih      integer. If >0 it indicates q[] is >= 0.5, hence
 *              it also indicates the *sign* of the result.
 *
 */
/*
 * Constants:
 * The hexadecimal values are the intended ones for the following
 * constants. The decimal values may be used, provided that the
 * compiler will convert from decimal to binary accurately enough
 * to produce the hexadecimal values shown.
 */

int __rem_pio2_large(double *x, double *y, int e0, int nx, int prec)
{
  static const int init_jk[] = {3,4,4,6}; /* initial value for jk */

  /*
   * Table of constants for 2/pi, 396 Hex digits (476 decimal) of 2/pi
   *
   *              integer array, contains the (24*i)-th to (24*i+23)-th
   *              bit of 2/pi after binary point. The corresponding
   *              floating value is
   *
   *                      ipio2[i] * 2^(-24(i+1)).
   *
   * NB: This table must have at least (e0-3)/24 + jk terms.
   *     For quad precision (e0 <= 16360, jk = 6), this is 686.
   */
  static const int32_t ipio2[] = {
  0xA2F983, 0x6E4E44, 0x1529FC, 0x2757D1, 0xF534DD, 0xC0DB62,
  0x95993C, 0x439041, 0xFE5163, 0xABDEBB, 0xC561B7, 0x246E3A,
  0x424DD2, 0xE00649, 0x2EEA09, 0xD1921C, 0xFE1DEB, 0x1CB129,
  0xA73EE8, 0x8235F5, 0x2EBB44, 0x84E99C, 0x7026B4, 0x5F7E41,
  0x3991D6, 0x398353, 0x39F49C, 0x845F8B, 0xBDF928, 0x3B1FF8,
  0x97FFDE, 0x05980F, 0xEF2F11, 0x8B5A0A, 0x6D1F6D, 0x367ECF,
  0x27CB09, 0xB74F46, 0x3F669E, 0x5FEA2D, 0x7527BA, 0xC7EBE5,
  0xF17B3D, 0x0739F7, 0x8A5292, 0xEA6BFB, 0x5FB11F, 0x8D5D08,
  0x560330, 0x46FC7B, 0x6BABF0, 0xCFBC20, 0x9AF436, 0x1DA9E3,
  0x91615E, 0xE61B08, 0x659985, 0x5F14A0, 0x68408D, 0xFFD880,
  0x4D7327, 0x310606, 0x1556CA, 0x73A8C9, 0x60E27B, 0xC08C6B,

  #if LDBL_MAX_EXP > 1024
  0x47C419, 0xC367CD, 0xDCE809, 0x2A8359, 0xC4768B, 0x961CA6,
  0xDDAF44, 0xD15719, 0x053EA5, 0xFF0705, 0x3F7E33, 0xE832C2,
  0xDE4F98, 0x327DBB, 0xC33D26, 0xEF6B1E, 0x5EF89F, 0x3A1F35,
  0xCAF27F, 0x1D87F1, 0x21907C, 0x7C246A, 0xFA6ED5, 0x772D30,
  0x433B15, 0xC614B5, 0x9D19C3, 0xC2C4AD, 0x414D2C, 0x5D000C,
  0x467D86, 0x2D71E3, 0x9AC69B, 0x006233, 0x7CD2B4, 0x97A7B4,
  0xD55537, 0xF63ED7, 0x1810A3, 0xFC764D, 0x2A9D64, 0xABD770,
  0xF87C63, 0x57B07A, 0xE71517, 0x5649C0, 0xD9D63B, 0x3884A7,
  0xCB2324, 0x778AD6, 0x23545A, 0xB91F00, 0x1B0AF1, 0xDFCE19,
  0xFF319F, 0x6A1E66, 0x615799, 0x47FBAC, 0xD87F7E, 0xB76522,
  0x89E832, 0x60BFE6, 0xCDC4EF, 0x09366C, 0xD43F5D, 0xD7DE16,
  0xDE3B58, 0x929BDE, 0x2822D2, 0xE88628, 0x4D58E2, 0x32CAC6,
  0x16E308, 0xCB7DE0, 0x50C017, 0xA71DF3, 0x5BE018, 0x34132E,
  0x621283, 0x014883, 0x5B8EF5, 0x7FB0AD, 0xF2E91E, 0x434A48,
  0xD36710, 0xD8DDAA, 0x425FAE, 0xCE616A, 0xA4280A, 0xB499D3,
  0xF2A606, 0x7F775C, 0x83C2A3, 0x883C61, 0x78738A, 0x5A8CAF,
  0xBDD76F, 0x63A62D, 0xCBBFF4, 0xEF818D, 0x67C126, 0x45CA55,
  0x36D9CA, 0xD2A828, 0x8D61C2, 0x77C912, 0x142604, 0x9B4612,
  0xC459C4, 0x44C5C8, 0x91B24D, 0xF31700, 0xAD43D4, 0xE54929,
  0x10D5FD, 0xFCBE00, 0xCC941E, 0xEECE70, 0xF53E13, 0x80F1EC,
  0xC3E7B3, 0x28F8C7, 0x940593, 0x3E71C1, 0xB3092E, 0xF3450B,
  0x9C1288, 0x7B20AB, 0x9FB52E, 0xC29247, 0x2F327B, 0x6D550C,
  0x90A772, 0x1FE76B, 0x96CB31, 0x4A1679, 0xE27941, 0x89DFF4,
  0x9794E8, 0x84E6E2, 0x973199, 0x6BED88, 0x365F5F, 0x0EFDBB,
  0xB49A48, 0x6CA467, 0x427271, 0x325D8D, 0xB8159F, 0x09E5BC,
  0x25318D, 0x3974F7, 0x1C0530, 0x010C0D, 0x68084B, 0x58EE2C,
  0x90AA47, 0x02E774, 0x24D6BD, 0xA67DF7, 0x72486E, 0xEF169F,
  0xA6948E, 0xF691B4, 0x5153D1, 0xF20ACF, 0x339820, 0x7E4BF5,
  0x6863B2, 0x5F3EDD, 0x035D40, 0x7F8985, 0x295255, 0xC06437,
  0x10D86D, 0x324832, 0x754C5B, 0xD4714E, 0x6E5445, 0xC1090B,
  0x69F52A, 0xD56614, 0x9D0727, 0x50045D, 0xDB3BB4, 0xC576EA,
  0x17F987, 0x7D6B49, 0xBA271D, 0x296996, 0xACCCC6, 0x5414AD,
  0x6AE290, 0x89D988, 0x50722C, 0xBEA404, 0x940777, 0x7030F3,
  0x27FC00, 0xA871EA, 0x49C266, 0x3DE064, 0x83DD97, 0x973FA3,
  0xFD9443, 0x8C860D, 0xDE4131, 0x9D3992, 0x8C70DD, 0xE7B717,
  0x3BDF08, 0x2B3715, 0xA0805C, 0x93805A, 0x921110, 0xD8E80F,
  0xAF806C, 0x4BFFDB, 0x0F9038, 0x761859, 0x15A562, 0xBBCB61,
  0xB989C7, 0xBD4010, 0x04F2D2, 0x277549, 0xF6B6EB, 0xBB22DB,
  0xAA140A, 0x2F2689, 0x768364, 0x333B09, 0x1A940E, 0xAA3A51,
  0xC2A31D, 0xAEEDAF, 0x12265C, 0x4DC26D, 0x9C7A2D, 0x9756C0,
  0x833F03, 0xF6F009, 0x8C402B, 0x99316D, 0x07B439, 0x15200C,
  0x5BC3D8, 0xC492F5, 0x4BADC6, 0xA5CA4E, 0xCD37A7, 0x36A9E6,
  0x9492AB, 0x6842DD, 0xDE6319, 0xEF8C76, 0x528B68, 0x37DBFC,
  0xABA1AE, 0x3115DF, 0xA1AE00, 0xDAFB0C, 0x664D64, 0xB705ED,
  0x306529, 0xBF5657, 0x3AFF47, 0xB9F96A, 0xF3BE75, 0xDF9328,
  0x3080AB, 0xF68C66, 0x15CB04, 0x0622FA, 0x1DE4D9, 0xA4B33D,
  0x8F1B57, 0x09CD36, 0xE9424E, 0xA4BE13, 0xB52333, 0x1AAAF0,
  0xA8654F, 0xA5C1D2, 0x0F3F0B, 0xCD785B, 0x76F923, 0x048B7B,
  0x721789, 0x53A6C6, 0xE26E6F, 0x00EBEF, 0x584A9B, 0xB7DAC4,
  0xBA66AA, 0xCFCF76, 0x1D02D1, 0x2DF1B1, 0xC1998C, 0x77ADC3,
  0xDA4886, 0xA05DF7, 0xF480C6, 0x2FF0AC, 0x9AECDD, 0xBC5C3F,
  0x6DDED0, 0x1FC790, 0xB6DB2A, 0x3A25A3, 0x9AAF00, 0x9353AD,
  0x0457B6, 0xB42D29, 0x7E804B, 0xA707DA, 0x0EAA76, 0xA1597B,
  0x2A1216, 0x2DB7DC, 0xFDE5FA, 0xFEDB89, 0xFDBE89, 0x6C76E4,
  0xFCA906, 0x70803E, 0x156E85, 0xFF87FD, 0x073E28, 0x336761,
  0x86182A, 0xEABD4D, 0xAFE7B3, 0x6E6D8F, 0x396795, 0x5BBF31,
  0x48D784, 0x16DF30, 0x432DC7, 0x356125, 0xCE70C9, 0xB8CB30,
  0xFD6CBF, 0xA200A4, 0xE46C05, 0xA0DD5A, 0x476F21, 0xD21262,
  0x845CB9, 0x496170, 0xE0566B, 0x015299, 0x375550, 0xB7D51E,
  0xC4F133, 0x5F6E13, 0xE4305D, 0xA92E85, 0xC3B21D, 0x3632A1,
  0xA4B708, 0xD4B1EA, 0x21F716, 0xE4698F, 0x77FF27, 0x80030C,
  0x2D408D, 0xA0CD4F, 0x99A520, 0xD3A2B3, 0x0A5D2F, 0x42F9B4,
  0xCBDA11, 0xD0BE7D, 0xC1DB9B, 0xBD17AB, 0x81A2CA, 0x5C6A08,
  0x17552E, 0x550027, 0xF0147F, 0x8607E1, 0x640B14, 0x8D4196,
  0xDEBE87, 0x2AFDDA, 0xB6256B, 0x34897B, 0xFEF305, 0x9EBFB9,
  0x4F6A68, 0xA82A4A, 0x5AC44F, 0xBCF82D, 0x985AD7, 0x95C7F4,
  0x8D4D0D, 0xA63A20, 0x5F57A4, 0xB13F14, 0x953880, 0x0120CC,
  0x86DD71, 0xB6DEC9, 0xF560BF, 0x11654D, 0x6B0701, 0xACB08C,
  0xD0C0B2, 0x485551, 0x0EFB1E, 0xC37295, 0x3B06A3, 0x3540C0,
  0x7BDC06, 0xCC45E0, 0xFA294E, 0xC8CAD6, 0x41F3E8, 0xDE647C,
  0xD8649B, 0x31BED9, 0xC397A4, 0xD45877, 0xC5E369, 0x13DAF0,
  0x3C3ABA, 0x461846, 0x5F7555, 0xF5BDD2, 0xC6926E, 0x5D2EAC,
  0xED440E, 0x423E1C, 0x87C461, 0xE9FD29, 0xF3D6E7, 0xCA7C22,
  0x35916F, 0xC5E008, 0x8DD7FF, 0xE26A6E, 0xC6FDB0, 0xC10893,
  0x745D7C, 0xB2AD6B, 0x9D6ECD, 0x7B723E, 0x6A11C6, 0xA9CFF7,
  0xDF7329, 0xBAC9B5, 0x5100B7, 0x0DB2E2, 0x24BA74, 0x607DE5,
  0x8AD874, 0x2C150D, 0x0C1881, 0x94667E, 0x162901, 0x767A9F,
  0xBEFDFD, 0xEF4556, 0x367ED9, 0x13D9EC, 0xB9BA8B, 0xFC97C4,
  0x27A831, 0xC36EF1, 0x36C594, 0x56A8D8, 0xB5A8B4, 0x0ECCCF,
  0x2D8912, 0x34576F, 0x89562C, 0xE3CE99, 0xB920D6, 0xAA5E6B,
  0x9C2A3E, 0xCC5F11, 0x4A0BFD, 0xFBF4E1, 0x6D3B8E, 0x2C86E2,
  0x84D4E9, 0xA9B4FC, 0xD1EEEF, 0xC9352E, 0x61392F, 0x442138,
  0xC8D91B, 0x0AFC81, 0x6A4AFB, 0xD81C2F, 0x84B453, 0x8C994E,
  0xCC2254, 0xDC552A, 0xD6C6C0, 0x96190B, 0xB8701A, 0x649569,
  0x605A26, 0xEE523F, 0x0F117F, 0x11B5F4, 0xF5CBFC, 0x2DBC34,
  0xEEBC34, 0xCC5DE8, 0x605EDD, 0x9B8E67, 0xEF3392, 0xB817C9,
  0x9B5861, 0xBC57E1, 0xC68351, 0x103ED8, 0x4871DD, 0xDD1C2D,
  0xA118AF, 0x462C21, 0xD7F359, 0x987AD9, 0xC0549E, 0xFA864F,
  0xFC0656, 0xAE79E5, 0x362289, 0x22AD38, 0xDC9367, 0xAAE855,
  0x382682, 0x9BE7CA, 0xA40D51, 0xB13399, 0x0ED7A9, 0x480569,
  0xF0B265, 0xA7887F, 0x974C88, 0x36D1F9, 0xB39221, 0x4A827B,
  0x21CF98, 0xDC9F40, 0x5547DC, 0x3A74E1, 0x42EB67, 0xDF9DFE,
  0x5FD45E, 0xA4677B, 0x7AACBA, 0xA2F655, 0x23882B, 0x55BA41,
  0x086E59, 0x862A21, 0x834739, 0xE6E389, 0xD49EE5, 0x40FB49,
  0xE956FF, 0xCA0F1C, 0x8A59C5, 0x2BFA94, 0xC5C1D3, 0xCFC50F,
  0xAE5ADB, 0x86C547, 0x624385, 0x3B8621, 0x94792C, 0x876110,
  0x7B4C2A, 0x1A2C80, 0x12BF43, 0x902688, 0x893C78, 0xE4C4A8,
  0x7BDBE5, 0xC23AC4, 0xEAF426, 0x8A67F7, 0xBF920D, 0x2BA365,
  0xB1933D, 0x0B7CBD, 0xDC51A4, 0x63DD27, 0xDDE169, 0x19949A,
  0x9529A8, 0x28CE68, 0xB4ED09, 0x209F44, 0xCA984E, 0x638270,
  0x237C7E, 0x32B90F, 0x8EF5A7, 0xE75614, 0x08F121, 0x2A9DB5,
  0x4D7E6F, 0x5119A5, 0xABF9B5, 0xD6DF82, 0x61DD96, 0x023616,
  0x9F3AC4, 0xA1A283, 0x6DED72, 0x7A8D39, 0xA9B882, 0x5C326B,
  0x5B2746, 0xED3400, 0x7700D2, 0x55F4FC, 0x4D5901, 0x8071E0,
  #endif
  };

  static const double PIo2[] = {
    1.57079625129699707031e+00, /* 0x3FF921FB, 0x40000000 */
    7.54978941586159635335e-08, /* 0x3E74442D, 0x00000000 */
    5.39030252995776476554e-15, /* 0x3CF84698, 0x80000000 */
    3.28200341580791294123e-22, /* 0x3B78CC51, 0x60000000 */
    1.27065575308067607349e-29, /* 0x39F01B83, 0x80000000 */
    1.22933308981111328932e-36, /* 0x387A2520, 0x40000000 */
    2.73370053816464559624e-44, /* 0x36E38222, 0x80000000 */
    2.16741683877804819444e-51, /* 0x3569F31D, 0x00000000 */
  };

  int32_t jz,jx,jv,jp,jk,carry,n,iq[20],i,j,k,m,q0,ih;
  double z,fw,f[20],fq[20],q[20];

  /* initialize jk*/
  jk = init_jk[prec];
  jp = jk;

  /* determine jx,jv,q0, note that 3>q0 */
  jx = nx-1;
  jv = (e0-3)/24;  if(jv<0) jv=0;
  q0 = e0-24*(jv+1);

  /* set up f[0] to f[jx+jk] where f[jx+jk] = ipio2[jv+jk] */
  j = jv-jx; m = jx+jk;
  for (i=0; i<=m; i++,j++)
    f[i] = j<0 ? 0.0 : (double)ipio2[j];

  /* compute q[0],q[1],...q[jk] */
  for (i=0; i<=jk; i++) {
    for (j=0,fw=0.0; j<=jx; j++)
      fw += x[j]*f[jx+i-j];
    q[i] = fw;
  }

  jz = jk;
recompute:
  /* distill q[] into iq[] reversingly */
  for (i=0,j=jz,z=q[jz]; j>0; i++,j--) {
    fw    = (double)(int32_t)(0x1p-24*z);
    iq[i] = (int32_t)(z - 0x1p24*fw);
    z     = q[j-1]+fw;
  }

  /* compute n */
  z  = scalbn(z,q0);       /* actual value of z */
  z -= 8.0*floor(z*0.125); /* trim off integer >= 8 */
  n  = (int32_t)z;
  z -= (double)n;
  ih = 0;
  if (q0 > 0) {  /* need iq[jz-1] to determine n */
    i  = iq[jz-1]>>(24-q0); n += i;
    iq[jz-1] -= i<<(24-q0);
    ih = iq[jz-1]>>(23-q0);
  }
  else if (q0 == 0) ih = iq[jz-1]>>23;
  else if (z >= 0.5) ih = 2;

  if (ih > 0) {  /* q > 0.5 */
    n += 1; carry = 0;
    for (i=0; i<jz; i++) {  /* compute 1-q */
      j = iq[i];
      if (carry == 0) {
        if (j != 0) {
          carry = 1;
          iq[i] = 0x1000000 - j;
        }
      } else
        iq[i] = 0xffffff - j;
    }
    if (q0 > 0) {  /* rare case: chance is 1 in 12 */
      switch(q0) {
      case 1:
        iq[jz-1] &= 0x7fffff; break;
      case 2:
        iq[jz-1] &= 0x3fffff; break;
      }
    }
    if (ih == 2) {
      z = 1.0 - z;
      if (carry != 0)
        z -= scalbn(1.0,q0);
    }
  }

  /* check if recomputation is needed */
  if (z == 0.0) {
    j = 0;
    for (i=jz-1; i>=jk; i--) j |= iq[i];
    if (j == 0) {  /* need recomputation */
      for (k=1; iq[jk-k]==0; k++);  /* k = no. of terms needed */

      for (i=jz+1; i<=jz+k; i++) {  /* add q[jz+1] to q[jz+k] */
        f[jx+i] = (double)ipio2[jv+i];
        for (j=0,fw=0.0; j<=jx; j++)
          fw += x[j]*f[jx+i-j];
        q[i] = fw;
      }
      jz += k;
      goto recompute;
    }
  }

  /* chop off zero terms */
  if (z == 0.0) {
    jz -= 1;
    q0 -= 24;
    while (iq[jz] == 0) {
      jz--;
      q0 -= 24;
    }
  } else { /* break z into 24-bit if necessary */
    z = scalbn(z,-q0);
    if (z >= 0x1p24) {
      fw = (double)(int32_t)(0x1p-24*z);
      iq[jz] = (int32_t)(z - 0x1p24*fw);
      jz += 1;
      q0 += 24;
      iq[jz] = (int32_t)fw;
    } else
      iq[jz] = (int32_t)z;
  }

  /* convert integer "bit" chunk to floating-point value */
  fw = scalbn(1.0,q0);
  for (i=jz; i>=0; i--) {
    q[i] = fw*(double)iq[i];
    fw *= 0x1p-24;
  }

  /* compute PIo2[0,...,jp]*q[jz,...,0] */
  for(i=jz; i>=0; i--) {
    for (fw=0.0,k=0; k<=jp && k<=jz-i; k++)
      fw += PIo2[k]*q[i+k];
    fq[jz-i] = fw;
  }

  /* compress fq[] into y[] */
  switch(prec) {
  case 0:
    fw = 0.0;
    for (i=jz; i>=0; i--)
      fw += fq[i];
    y[0] = ih==0 ? fw : -fw;
    break;
  case 1:
  case 2:
    fw = 0.0;
    for (i=jz; i>=0; i--)
      fw += fq[i];
    // TODO: drop excess precision here once double_t is used
    fw = (double)fw;
    y[0] = ih==0 ? fw : -fw;
    fw = fq[0]-fw;
    for (i=1; i<=jz; i++)
      fw += fq[i];
    y[1] = ih==0 ? fw : -fw;
    break;
  case 3:  /* painful */
    for (i=jz; i>0; i--) {
      fw      = fq[i-1]+fq[i];
      fq[i]  += fq[i-1]-fw;
      fq[i-1] = fw;
    }
    for (i=jz; i>1; i--) {
      fw      = fq[i-1]+fq[i];
      fq[i]  += fq[i-1]-fw;
      fq[i-1] = fw;
    }
    for (fw=0.0,i=jz; i>=2; i--)
      fw += fq[i];
    if (ih==0) {
      y[0] =  fq[0]; y[1] =  fq[1]; y[2] =  fw;
    } else {
      y[0] = -fq[0]; y[1] = -fq[1]; y[2] = -fw;
    }
  }
  return n&7;
}
// musl file end: src/math/__rem_pio2_large.c

// musl file begin: src/math/__rem_pio2.c
/* origin: FreeBSD /usr/src/lib/msun/src/e_rem_pio2.c */
/*
 * ====================================================
 * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
 *
 * Developed at SunSoft, a Sun Microsystems, Inc. business.
 * Permission to use, copy, modify, and distribute this
 * software is freely granted, provided that this notice
 * is preserved.
 * ====================================================
 *
 * Optimized by Bruce D. Evans.
 */
/* __rem_pio2(x,y)
 *
 * return the remainder of x rem pi/2 in y[0]+y[1]
 * use __rem_pio2_large() for large x
 */

/* caller must handle the case when reduction is not needed: |x| ~<= pi/4 */
int __rem_pio2(double x, double *y)
{
  /*
   * invpio2:  53 bits of 2/pi
   * pio2_1:   first  33 bit of pi/2
   * pio2_1t:  pi/2 - pio2_1
   * pio2_2:   second 33 bit of pi/2
   * pio2_2t:  pi/2 - (pio2_1+pio2_2)
   * pio2_3:   third  33 bit of pi/2
   * pio2_3t:  pi/2 - (pio2_1+pio2_2+pio2_3)
   */
  static const double
  toint   = 1.5/EPS,
  pio4    = 0x1.921fb54442d18p-1,
  invpio2 = 6.36619772367581382433e-01, /* 0x3FE45F30, 0x6DC9C883 */
  pio2_1  = 1.57079632673412561417e+00, /* 0x3FF921FB, 0x54400000 */
  pio2_1t = 6.07710050650619224932e-11, /* 0x3DD0B461, 0x1A626331 */
  pio2_2  = 6.07710050630396597660e-11, /* 0x3DD0B461, 0x1A600000 */
  pio2_2t = 2.02226624879595063154e-21, /* 0x3BA3198A, 0x2E037073 */
  pio2_3  = 2.02226624871116645580e-21, /* 0x3BA3198A, 0x2E000000 */
  pio2_3t = 8.47842766036889956997e-32; /* 0x397B839A, 0x252049C1 */

  union {double f; uint64_t i;} u = {x};
  double_t z,w,t,r,fn;
  double tx[3],ty[2];
  uint32_t ix;
  int sign, n, ex, ey, i;

  sign = u.i>>63;
  ix = u.i>>32 & 0x7fffffff;
  if (ix <= 0x400f6a7a) {  /* |x| ~<= 5pi/4 */
    if ((ix & 0xfffff) == 0x921fb)  /* |x| ~= pi/2 or 2pi/2 */
      goto medium;  /* cancellation -- use medium case */
    if (ix <= 0x4002d97c) {  /* |x| ~<= 3pi/4 */
      if (!sign) {
        z = x - pio2_1;  /* one round good to 85 bits */
        y[0] = z - pio2_1t;
        y[1] = (z-y[0]) - pio2_1t;
        return 1;
      } else {
        z = x + pio2_1;
        y[0] = z + pio2_1t;
        y[1] = (z-y[0]) + pio2_1t;
        return -1;
      }
    } else {
      if (!sign) {
        z = x - 2*pio2_1;
        y[0] = z - 2*pio2_1t;
        y[1] = (z-y[0]) - 2*pio2_1t;
        return 2;
      } else {
        z = x + 2*pio2_1;
        y[0] = z + 2*pio2_1t;
        y[1] = (z-y[0]) + 2*pio2_1t;
        return -2;
      }
    }
  }
  if (ix <= 0x401c463b) {  /* |x| ~<= 9pi/4 */
    if (ix <= 0x4015fdbc) {  /* |x| ~<= 7pi/4 */
      if (ix == 0x4012d97c)  /* |x| ~= 3pi/2 */
        goto medium;
      if (!sign) {
        z = x - 3*pio2_1;
        y[0] = z - 3*pio2_1t;
        y[1] = (z-y[0]) - 3*pio2_1t;
        return 3;
      } else {
        z = x + 3*pio2_1;
        y[0] = z + 3*pio2_1t;
        y[1] = (z-y[0]) + 3*pio2_1t;
        return -3;
      }
    } else {
      if (ix == 0x401921fb)  /* |x| ~= 4pi/2 */
        goto medium;
      if (!sign) {
        z = x - 4*pio2_1;
        y[0] = z - 4*pio2_1t;
        y[1] = (z-y[0]) - 4*pio2_1t;
        return 4;
      } else {
        z = x + 4*pio2_1;
        y[0] = z + 4*pio2_1t;
        y[1] = (z-y[0]) + 4*pio2_1t;
        return -4;
      }
    }
  }
  if (ix < 0x413921fb) {  /* |x| ~< 2^20*(pi/2), medium size */
medium:
    /* rint(x/(pi/2)) */
    fn = (double_t)x*invpio2 + toint - toint;
    n = (int32_t)fn;
    r = x - fn*pio2_1;
    w = fn*pio2_1t;  /* 1st round, good to 85 bits */
    /* Matters with directed rounding. */
    if (predict_false(r - w < -pio4)) {
      n--;
      fn--;
      r = x - fn*pio2_1;
      w = fn*pio2_1t;
    } else if (predict_false(r - w > pio4)) {
      n++;
      fn++;
      r = x - fn*pio2_1;
      w = fn*pio2_1t;
    }
    y[0] = r - w;
    u.f = y[0];
    ey = u.i>>52 & 0x7ff;
    ex = ix>>20;
    if (ex - ey > 16) { /* 2nd round, good to 118 bits */
      t = r;
      w = fn*pio2_2;
      r = t - w;
      w = fn*pio2_2t - ((t-r)-w);
      y[0] = r - w;
      u.f = y[0];
      ey = u.i>>52 & 0x7ff;
      if (ex - ey > 49) {  /* 3rd round, good to 151 bits, covers all cases */
        t = r;
        w = fn*pio2_3;
        r = t - w;
        w = fn*pio2_3t - ((t-r)-w);
        y[0] = r - w;
      }
    }
    y[1] = (r - y[0]) - w;
    return n;
  }
  /*
   * all other (large) arguments
   */
  if (ix >= 0x7ff00000) {  /* x is inf or NaN */
    y[0] = y[1] = x - x;
    return 0;
  }
  /* set z = scalbn(|x|,-ilogb(x)+23) */
  u.f = x;
  u.i &= (uint64_t)-1>>12;
  u.i |= (uint64_t)(0x3ff + 23)<<52;
  z = u.f;
  for (i=0; i < 2; i++) {
    tx[i] = (double)(int32_t)z;
    z     = (z-tx[i])*0x1p24;
  }
  tx[i] = z;
  /* skip zero terms, first term is non-zero */
  while (tx[i] == 0.0)
    i--;
  n = __rem_pio2_large(tx,ty,(int)(ix>>20)-(0x3ff+23),i+1,1);
  if (sign) {
    y[0] = -ty[0];
    y[1] = -ty[1];
    return -n;
  }
  y[0] = ty[0];
  y[1] = ty[1];
  return n;
}
// musl file end: src/math/__rem_pio2.c

// musl file begin: src/math/__cos.c
/* origin: FreeBSD /usr/src/lib/msun/src/k_cos.c */
/*
 * ====================================================
 * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
 *
 * Developed at SunSoft, a Sun Microsystems, Inc. business.
 * Permission to use, copy, modify, and distribute this
 * software is freely granted, provided that this notice
 * is preserved.
 * ====================================================
 */
/*
 * __cos( x,  y )
 * kernel cos function on [-pi/4, pi/4], pi/4 ~ 0.785398164
 * Input x is assumed to be bounded by ~pi/4 in magnitude.
 * Input y is the tail of x.
 *
 * Algorithm
 *      1. Since cos(-x) = cos(x), we need only to consider positive x.
 *      2. if x < 2^-27 (hx<0x3e400000 0), return 1 with inexact if x!=0.
 *      3. cos(x) is approximated by a polynomial of degree 14 on
 *         [0,pi/4]
 *                                       4            14
 *              cos(x) ~ 1 - x*x/2 + C1*x + ... + C6*x
 *         where the remez error is
 *
 *      |              2     4     6     8     10    12     14 |     -58
 *      |cos(x)-(1-.5*x +C1*x +C2*x +C3*x +C4*x +C5*x  +C6*x  )| <= 2
 *      |                                                      |
 *
 *                     4     6     8     10    12     14
 *      4. let r = C1*x +C2*x +C3*x +C4*x +C5*x  +C6*x  , then
 *             cos(x) ~ 1 - x*x/2 + r
 *         since cos(x+y) ~ cos(x) - sin(x)*y
 *                        ~ cos(x) - x*y,
 *         a correction term is necessary in cos(x) and hence
 *              cos(x+y) = 1 - (x*x/2 - (r - x*y))
 *         For better accuracy, rearrange to
 *              cos(x+y) ~ w + (tmp + (r-x*y))
 *         where w = 1 - x*x/2 and tmp is a tiny correction term
 *         (1 - x*x/2 == w + tmp exactly in infinite precision).
 *         The exactness of w + tmp in infinite precision depends on w
 *         and tmp having the same precision as x.  If they have extra
 *         precision due to compiler bugs, then the extra precision is
 *         only good provided it is retained in all terms of the final
 *         expression for cos().  Retention happens in all cases tested
 *         under FreeBSD, so don't pessimize things by forcibly clipping
 *         any extra precision in w.
 */

double __cos(double x, double y)
{
  static const double
  C1  =  4.16666666666666019037e-02, /* 0x3FA55555, 0x5555554C */
  C2  = -1.38888888888741095749e-03, /* 0xBF56C16C, 0x16C15177 */
  C3  =  2.48015872894767294178e-05, /* 0x3EFA01A0, 0x19CB1590 */
  C4  = -2.75573143513906633035e-07, /* 0xBE927E4F, 0x809C52AD */
  C5  =  2.08757232129817482790e-09, /* 0x3E21EE9E, 0xBDB4B1C4 */
  C6  = -1.13596475577881948265e-11; /* 0xBDA8FAE9, 0xBE8838D4 */

  double_t hz,z,r,w;

  z  = x*x;
  w  = z*z;
  r  = z*(C1+z*(C2+z*C3)) + w*w*(C4+z*(C5+z*C6));
  hz = 0.5*z;
  w  = 1.0-hz;
  return w + (((1.0-w)-hz) + (z*r-x*y));
}
// musl file end: src/math/__cos.c

// musl file begin: src/math/__sin.c
/* origin: FreeBSD /usr/src/lib/msun/src/k_sin.c */
/*
 * ====================================================
 * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
 *
 * Developed at SunSoft, a Sun Microsystems, Inc. business.
 * Permission to use, copy, modify, and distribute this
 * software is freely granted, provided that this notice
 * is preserved.
 * ====================================================
 */
/* __sin( x, y, iy)
 * kernel sin function on ~[-pi/4, pi/4] (except on -0), pi/4 ~ 0.7854
 * Input x is assumed to be bounded by ~pi/4 in magnitude.
 * Input y is the tail of x.
 * Input iy indicates whether y is 0. (if iy=0, y assume to be 0).
 *
 * Algorithm
 *      1. Since sin(-x) = -sin(x), we need only to consider positive x.
 *      2. Callers must return sin(-0) = -0 without calling here since our
 *         odd polynomial is not evaluated in a way that preserves -0.
 *         Callers may do the optimization sin(x) ~ x for tiny x.
 *      3. sin(x) is approximated by a polynomial of degree 13 on
 *         [0,pi/4]
 *                               3            13
 *              sin(x) ~ x + S1*x + ... + S6*x
 *         where
 *
 *      |sin(x)         2     4     6     8     10     12  |     -58
 *      |----- - (1+S1*x +S2*x +S3*x +S4*x +S5*x  +S6*x   )| <= 2
 *      |  x                                               |
 *
 *      4. sin(x+y) = sin(x) + sin'(x')*y
 *                  ~ sin(x) + (1-x*x/2)*y
 *         For better accuracy, let
 *                   3      2      2      2      2
 *              r = x *(S2+x *(S3+x *(S4+x *(S5+x *S6))))
 *         then                   3    2
 *              sin(x) = x + (S1*x + (x *(r-y/2)+y))
 */

double __sin(double x, double y, int iy)
{
  static const double
  S1  = -1.66666666666666324348e-01, /* 0xBFC55555, 0x55555549 */
  S2  =  8.33333333332248946124e-03, /* 0x3F811111, 0x1110F8A6 */
  S3  = -1.98412698298579493134e-04, /* 0xBF2A01A0, 0x19C161D5 */
  S4  =  2.75573137070700676789e-06, /* 0x3EC71DE3, 0x57B1FE7D */
  S5  = -2.50507602534068634195e-08, /* 0xBE5AE5E6, 0x8A2B9CEB */
  S6  =  1.58969099521155010221e-10; /* 0x3DE5D93A, 0x5ACFD57C */

  double_t z,r,v,w;

  z = x*x;
  w = z*z;
  r = S2 + z*(S3 + z*S4) + z*w*(S5 + z*S6);
  v = z*x;
  if (iy == 0)
    return x + v*(S1 + z*r);
  else
    return x - ((z*(0.5*y - v*r) - y) - v*S1);
}
// musl file end: src/math/__sin.c

// musl file begin: src/math/sin.c
/* origin: FreeBSD /usr/src/lib/msun/src/s_sin.c */
/*
 * ====================================================
 * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
 *
 * Developed at SunPro, a Sun Microsystems, Inc. business.
 * Permission to use, copy, modify, and distribute this
 * software is freely granted, provided that this notice
 * is preserved.
 * ====================================================
 */
/* sin(x)
 * Return sine function of x.
 *
 * kernel function:
 *      __sin            ... sine function on [-pi/4,pi/4]
 *      __cos            ... cose function on [-pi/4,pi/4]
 *      __rem_pio2       ... argument reduction routine
 *
 * Method.
 *      Let S,C and T denote the sin, cos and tan respectively on
 *      [-PI/4, +PI/4]. Reduce the argument x to y1+y2 = x-k*pi/2
 *      in [-pi/4 , +pi/4], and let n = k mod 4.
 *      We have
 *
 *          n        sin(x)      cos(x)        tan(x)
 *     ----------------------------------------------------------
 *          0          S           C             T
 *          1          C          -S            -1/T
 *          2         -S          -C             T
 *          3         -C           S            -1/T
 *     ----------------------------------------------------------
 *
 * Special cases:
 *      Let trig be any of sin, cos, or tan.
 *      trig(+-INF)  is NaN, with signals;
 *      trig(NaN)    is that NaN;
 *
 * Accuracy:
 *      TRIG(x) returns trig(x) nearly rounded
 */

double mr_musl::math::sin(double x)
{
  double y[2];
  uint32_t ix;
  unsigned n;

  /* High word of x. */
  GET_HIGH_WORD(ix, x);
  ix &= 0x7fffffff;

  /* |x| ~< pi/4 */
  if (ix <= 0x3fe921fb) {
    if (ix < 0x3e500000) {  /* |x| < 2**-26 */
      /* raise inexact if x != 0 and underflow if subnormal*/
      FORCE_EVAL(ix < 0x00100000 ? x/0x1p120f : x+0x1p120f);
      return x;
    }
    return __sin(x, 0.0, 0);
  }

  /* sin(Inf or NaN) is NaN */
  if (ix >= 0x7ff00000)
    return x - x;

  /* argument reduction needed */
  n = __rem_pio2(x, y);
  switch (n&3) {
  case 0: return  __sin(y[0], y[1], 1);
  case 1: return  __cos(y[0], y[1]);
  case 2: return -__sin(y[0], y[1], 1);
  default:
    return -__cos(y[0], y[1]);
  }
}
// musl file end: src/math/sin.c

#endif // MR_MUSL_IMPLEMENTATION

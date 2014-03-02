/*
 * This file is part of OpenModelica.
 *
 * Copyright (c) 1998-CurrentYear, Linköping University,
 * Department of Computer and Information Science,
 * SE-58183 Linköping, Sweden.
 *
 * All rights reserved.
 *
 * THIS PROGRAM IS PROVIDED UNDER THE TERMS OF GPL VERSION 3
 * AND THIS OSMC PUBLIC LICENSE (OSMC-PL).
 * ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES RECIPIENT'S
 * ACCEPTANCE OF THE OSMC PUBLIC LICENSE.
 *
 * The OpenModelica software and the Open Source Modelica
 * Consortium (OSMC) Public License (OSMC-PL) are obtained
 * from Linköping University, either from the above address,
 * from the URLs: http://www.ida.liu.se/projects/OpenModelica or
 * http://www.openmodelica.org, and in the OpenModelica distribution.
 * GNU version 3 is obtained from: http://www.gnu.org/copyleft/gpl.html.
 *
 * This program is distributed WITHOUT ANY WARRANTY; without
 * even the implied warranty of  MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE, EXCEPT AS EXPRESSLY SET FORTH
 * IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE CONDITIONS
 * OF OSMC-PL.
 *
 * See the full OSMC Public License conditions for more details.
 *
 */


#ifndef OMC_ERROR_H
#define OMC_ERROR_H

#include "openmodelica.h"
#include "omc_msvc.h"

#include <setjmp.h>
#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct _FILE_INFO
{
  const char* filename;
  int lineStart;
  int colStart;
  int lineEnd;
  int colEnd;
  int readonly;
} FILE_INFO;

#define omc_dummyFileInfo {"",-1,-1,-1,-1,1}

extern void printInfo(FILE *stream, FILE_INFO info);
extern void (*omc_assert)(threadData_t*,FILE_INFO,const char*, ...);
extern void (*omc_assert_warning)(FILE_INFO,const char*, ...);
extern void (*omc_terminate)(FILE_INFO,const char*, ...);
extern void (*omc_throw)(threadData_t*);
void initDumpSystem();
void omc_assert_function(threadData_t*,FILE_INFO info, const char *msg, ...);
void omc_assert_warning_function(FILE_INFO info, const char *msg, ...);
void omc_terminate_function(FILE_INFO info, const char *msg, ...);
void omc_throw_function(threadData_t*);

/* #define USE_DEBUG_OUTPUT */

enum LOG_STREAM
{
  LOG_UNKNOWN = 0,
  LOG_STDOUT,
  LOG_ASSERT,

  LOG_DDASRT,
  LOG_DEBUG,
  LOG_DSS,
  LOG_DSS_JAC,
  LOG_EVENTS,
  LOG_EVENTS_V,
  LOG_INIT,
  LOG_IPOPT,
  LOG_IPOPT_FULL,
  LOG_IPOPT_JAC,
  LOG_IPOPT_HESSE,
  LOG_IPOPT_ERROR,
  LOG_JAC,
  LOG_LS,
  LOG_LS_V,
  LOG_NLS,
  LOG_NLS_V,
  LOG_NLS_JAC,
  LOG_NLS_RES,
  LOG_RES_INIT,
  LOG_SIMULATION,
  LOG_SOLVER,
  LOG_SOTI,
  LOG_STATS,
  LOG_UTIL,
  LOG_ZEROCROSSINGS,

  LOG_MAX
};

extern const int firstOMCErrorStream;
extern const char *LOG_STREAM_NAME[LOG_MAX];
extern const char *LOG_STREAM_DESC[LOG_MAX];
extern const char *LOG_STREAM_DETAILED_DESC[LOG_MAX];

enum LOG_TYPE
{
  LOG_TYPE_UNKNOWN = 0,
  LOG_TYPE_INFO,
  LOG_TYPE_WARNING,
  LOG_TYPE_ERROR,
  LOG_TYPE_ASSERT,
  LOG_TYPE_DEBUG,
  LOG_TYPE_MAX
};

extern int useStream[LOG_MAX];
extern int level[LOG_MAX];
extern int lastType[LOG_MAX];
extern int lastStream;
extern int showAllWarnings;
extern char logBuffer[2048];

void setStreamPrintXML(int isXML);

#define ACTIVE_STREAM(stream)    (useStream[stream])
#define ACTIVE_WARNING_STREAM(stream)    (showAllWarnings || useStream[stream])

#ifdef USE_DEBUG_OUTPUT
  #define DEBUG_STREAM(stream)    (useStream[stream])
#else
  #define DEBUG_STREAM(stream)    (0)
#endif

extern void (*messageClose)(int stream);
extern void infoStreamPrint(int stream, int indentNext, const char *format, ...) __attribute__ ((format (printf, 3, 4)));
extern void infoStreamPrintWithEquationIndexes(int stream, int indentNext, const int *indexes, const char *format, ...) __attribute__ ((format (printf, 4, 5)));
extern void warningStreamPrint(int stream, int indentNext, const char *format, ...) __attribute__ ((format (printf, 3, 4)));
extern void warningStreamPrintWithEquationIndexes(int stream, int indentNext, const int *indexes, const char *format, ...) __attribute__ ((format (printf, 4, 5)));
extern void errorStreamPrint(int stream, int indentNext, const char *format, ...) __attribute__ ((format (printf, 3, 4)));
extern void assertStreamPrint(threadData_t *threadData, int cond, const char *format, ...) __attribute__ ((format (printf, 3, 4)));
extern void throwStreamPrint(threadData_t *threadData, const char *format, ...) __attribute__ ((format (printf, 2, 3), noreturn));
extern void throwStreamPrintWithEquationIndexes(threadData_t *threadData, const int *indexes, const char *format, ...) __attribute__ ((format (printf, 3, 4), noreturn));

#ifdef USE_DEBUG_OUTPUT
void debugStreamPrint(int stream, int indentNext, const char *format, ...) __attribute__ ((format (printf, 3, 4)));
void debugStreamPrintWithEquationIndexes(int stream, int indentNext, const int *indexes, const char *format, ...) __attribute__ ((format (printf, 4, 5)));
#else
static OMC_INLINE void debugStreamPrint(int stream, int indentNext, const char *format, ...) __attribute__ ((format (printf, 3, 4)));
static OMC_INLINE void debugStreamPrint(int stream, int indentNext, const char *format, ...) {/* Do nothing */}
static OMC_INLINE void debugStreamPrintWithEquationIndexes(int stream, int indentNext, const int *indexes, const char *format, ...) __attribute__ ((format (printf, 4, 5)));
static OMC_INLINE void debugStreamPrintWithEquationIndexes(int stream, int indentNext, const int *indexes, const char *format, ...)  {/* Do nothing */}
#endif

#ifdef __cplusplus
}
#endif

#endif

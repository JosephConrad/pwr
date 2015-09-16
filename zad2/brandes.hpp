#ifndef BRANDES_H_
#define BRANDES_H_

#include <CL/cl.h>
#include <string.h>
#include <cstdlib>
#include <iostream>
#include <string>
#include <fstream>

/*** GLOBALS ***/

//******************************************************************************
//						 Input data is stored here.
//*****************************************************************************/
char* inputName;
char* outputName;
cl_uint *input;
cl_uint *output;

cl_uint *sig;
cl_uint *dd;
cl_float *delta;
cl_float *C;
cl_uint *cont;

cl_mem inputBuffer;
cl_mem outputBuffer;
cl_kernel kernel;
//******************************************************************************
// 							Used buffers
//*****************************************************************************/
cl_mem   sigma;
cl_mem   d; //dist_ b = d_b
cl_mem   delta_b;
cl_mem   C_b;
cl_mem   cont_b;//bufor jedno elementowy do_continue

cl_mem   vptrs_b;
cl_mem   adjs_b;
cl_mem   vmap_b;
//******************************************************************************
// 			 Output data is stored here, tables are here
//*****************************************************************************/
cl_uint *vptrs, *adjs, *vmap;

cl_float *bc;

//******************************************************************************
// 				 Multiplier is stored in this variable 
//*****************************************************************************/
cl_uint multiplier;

cl_uint width;
cl_uint maxVer; //liczba wierzcholkow naszego grafu
//cl_uint l; //aktualny numer wierzcholka



cl_context          context;
cl_device_id        *devices;
cl_command_queue    commandQueue;
cl_program          program;

//******************************************************************************
// This program uses fivd kernel and this serves as a handle to it */
//*****************************************************************************/
cl_kernel  init_array, forward, middle, backward, final;


//******************************************************************************
//						 FUNCTION DECLARATIONS
//*****************************************************************************/

/*******************************************************************************
 * OpenCL related initialisations are done here.
 * Context, Device list, Command Queue are set up.
 * Calls are made to set up OpenCL memory buffers that this program uses
 * and to load the programs into memory and get kernel handles.
*******************************************************************************/
int initializeCL(void);

/*******************************************************************************
 * This is called once the OpenCL context, memory etc. are set up,
 * the program is loaded into memory and the kernel handles are ready.
 * 
 * It sets the values for kernels' arguments and enqueues calls to the kernels
 * on to the command queue and waits till the calls have finished execution.
 *
 * It also gets kernel start and end time if profiling is enabled.
*******************************************************************************/
int runCLKernels(void);

//******************************************************************************
/* Releases OpenCL resources (Context, Memory etc.) */
//******************************************************************************
int cleanupCL(void);

//******************************************************************************
/* Releases program's resources */
//******************************************************************************
void cleanupHost(void);

/*******************************************************************************
 * Prints no more than 256 elements of the given array.
 * Prints full array if length is less than 256.
 *
 * Prints Array name followed by elements.
*******************************************************************************/
void print1DArray(
		 const std::string arrayName, 
         const unsigned int * arrayData, 
         const unsigned int length);

std::string convertToString(const char * filename);

#endif  /* #ifndef BRANDES_H_ */

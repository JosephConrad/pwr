#include "brandes.hpp"
#include <iostream>
#include <stack>
#include "stdio.h"
#include <vector>
#include <math.h>
#include <queue>
#include <cstdio>
#include <set>
#include <fstream>
#include <algorithm>
#include <map>
/*
 * \brief Host Initialization 
 *        Allocate and initialize memory 
 *        on the host. Print input array. 
 */
using namespace std;

typedef long long LL;
const int DEBUG = 0;
#define PB push_back  
#define MP make_pair
#define ST first
#define ND second

#define REPF(i,n) for (int i=1; i<=n; i++)
#define REP(i,n) for (int i=0; i<n; i++)
#define FORD(i,a,b) for(int i=(a);i>=(b);--i)
#define FOR(i,a,b) for(int i=(a);i<=(b);++i)

#define FOREACH(i,s) for(VAR(i,(s).begin()); i != (s).end(); i++)
#define VAR(a,b)  __typeof(b) a=(b)
 
//*****************************************************************************
//                            Defined structures
//*****************************************************************************
map<int, vector<int> > graph;
std::vector<int> num_neigh;
const int MAX_NEIGH = 16;
cl_uint num_vertex;
cl_uint num_edges;
cl_uint num_virtual = 0;
std::string error;
//*****************************************************************************
//                               Function headers
//*****************************************************************************
cl_uint set_all_args();
cl_uint check_float(cl_float* pointer);
cl_uint check_status(cl_int status, std::string text);
cl_uint check_kern(cl_uint status);
cl_uint check(cl_uint* pointer);
cl_int set_arg (cl_kernel kernel, cl_uint ind, size_t size, const void *value);
cl_int set_arg_int (cl_kernel kernel, cl_uint ind, size_t size, cl_uint  value);
cl_int dev_info(cl_device_info param_name, size_t param_value_size, void *param_value);
cl_int enqueue_kernel ( cl_command_queue command_queue,
    cl_kernel kernel,
    cl_uint work_dim,
    const size_t *global_work_offset,
    const size_t *global_work_size,
    const size_t *local_work_size,
    cl_uint num_events_in_wait_list,
    const cl_event *event_wait_list,
    cl_event *event);
cl_int wait_ev(cl_uint num_events, const cl_event *event_list);
cl_int release_ev (cl_event event);
void print1DArray(
		 const std::string arrayName, 
         const unsigned int * arrayData, 
         const unsigned int length);
void verify();
void print_graph();
void print_vec(std::vector<int> array);
void print_array(cl_uint* array, int num_virtual);
int readData(char* fileName);
int cleanupCL(void);
void cleanupHost(void);
std::string convertToString(const char *filename);
// !!! maksymalny numer wierzcholka jest o jeden mniejszy od liczby wierzcholk

map< int, vector<int> >::iterator it;



//*****************************************************************************
//               Allocate and initialize memory used by host 
//*****************************************************************************
int initializeHost(void)
{
	sig				= NULL;

    cl_uint size = sizeof(cl_uint);

    sig = (cl_uint *) calloc(num_vertex, size);
    if (check(sig)) return 1;
    dd = (cl_uint *) calloc(num_vertex, size);
    if (check(dd)) return 1;
    cl_uint sizefloat = sizeof(cl_float);
    delta = (cl_float *) calloc(num_vertex, sizefloat);
    if (check_float(delta)) return 1;
   
    C = (cl_float *) calloc(num_vertex, sizefloat);
    if (check_float(delta)) return 1;


    cont = (cl_uint *) calloc(1, sizeof(cl_uint));
    if (check_float(delta)) return 1;

    return 0;
}

//*****************************************************************************
// * \brief OpenCL related initialization 
// *        Create Context, Device list, Command Queue
// *        Create OpenCL memory buffer objects
// *        Load CL file, compile, link CL source 
// *		  Build program and kernel objects
//*****************************************************************************
int initializeCL(void)
{
    cl_int status = 0;
    size_t deviceListSize;

    cl_uint numPlatforms;
    cl_platform_id platform = NULL;
    status = clGetPlatformIDs(0, NULL, &numPlatforms);
    if(status != CL_SUCCESS)
    {
        std::cout << "Error: Getting Platforms. (clGetPlatformsIDs)\n";
        return 1;
    }
    
    if(numPlatforms > 0)
    {
        cl_platform_id* platforms = new cl_platform_id[numPlatforms];
        status = clGetPlatformIDs(numPlatforms, platforms, NULL);
        if(status != CL_SUCCESS)
        {
            std::cout << "Error: Getting Platform Ids. (clGetPlatformsIDs)\n";
            return 1;
        }
        for(unsigned int i=0; i < numPlatforms; ++i)
        {
            char pbuff[100];
            status = clGetPlatformInfo(
                        platforms[i],
                        CL_PLATFORM_VENDOR,
                        sizeof(pbuff),
                        pbuff,
                        NULL);
            if(status != CL_SUCCESS)
            {
                std::cout << "Error: Getting Platform Info.(clGetPlatformInfo)\n";
                return 1;
            }
            platform = platforms[i];
            if(!strcmp(pbuff, "NVIDIA Corporation"))
            {
                break;
            }
        }
        delete platforms;
    }

    if(NULL == platform)
    {
        std::cout << "NULL platform found so Exiting Application." << std::endl;
        return 1;
    }

    
    // If we could find our platform, use it. Otherwise use just available platform.
    cl_context_properties cps[3] = { CL_CONTEXT_PLATFORM, (cl_context_properties)platform, 0 };

	/////////////////////////////////////////////////////////////////
	// Create an OpenCL context
	/////////////////////////////////////////////////////////////////
    context = clCreateContextFromType(cps, CL_DEVICE_TYPE_GPU, 
                                      NULL, NULL, &status);
    error = "Error: Creating Context. (clCreateContextFromType)\n";
    if (check_status(status, error)) return 1;

    /* First, get the size of device list data */
    status = clGetContextInfo(context, CL_CONTEXT_DEVICES, 0, NULL, 
                              &deviceListSize);
    error = "Error: Getting Context Info \
		    (device list size, clGetContextInfo)\n";
    if (check_status(status, error)) return 1;

	/////////////////////////////////////////////////////////////////
	// Detect OpenCL devices
	/////////////////////////////////////////////////////////////////
    devices = (cl_device_id *)malloc(deviceListSize);
	if(devices == 0) {
		std::cout<<"Error: No devices found.\n";
		return 1;
	}

    /* Now, get the device list data */
    status = clGetContextInfo(context, CL_CONTEXT_DEVICES, deviceListSize, 
                 devices, NULL);
    error = "Error: Getting Context Info \
		    (device list, clGetContextInfo)\n";
    if (check_status(status, error)) return 1;

	/////////////////////////////////////////////////////////////////
	// Create an OpenCL command queue
	/////////////////////////////////////////////////////////////////
    commandQueue = clCreateCommandQueue(context, devices[0], 0, &status);
	error = "Creating Command Queue. (clCreateCommandQueue)\n";
    if (check_status(status, error)) return 1;

    sigma = clCreateBuffer(context, CL_MEM_READ_WRITE | CL_MEM_USE_HOST_PTR,
                       sizeof(cl_uint) * num_vertex, sig, &status);

    d = clCreateBuffer(context, CL_MEM_READ_WRITE | CL_MEM_USE_HOST_PTR,
                       sizeof(cl_uint) * num_vertex, dd, &status);
    if (check_status(status, error)) return 1;

    delta_b = clCreateBuffer(context, CL_MEM_READ_WRITE | CL_MEM_USE_HOST_PTR,
                       sizeof(cl_float) * num_vertex, delta, &status);
    if (check_status(status, error)) return 1;

    C_b = clCreateBuffer(context, CL_MEM_READ_WRITE | CL_MEM_USE_HOST_PTR,
                       sizeof(cl_float) * num_vertex, C, &status);
    if (check_status(status, error)) return 1;
    
    cont_b = clCreateBuffer(context, CL_MEM_READ_WRITE | CL_MEM_USE_HOST_PTR,
                       sizeof(cl_uint), cont, &status);
    if (check_status(status, error)) return 1;
    
    
    
    vptrs_b = clCreateBuffer(context, CL_MEM_READ_WRITE | CL_MEM_USE_HOST_PTR,
                       sizeof(cl_uint) * (num_virtual + 1), vptrs, &status);
    if (check_status(status, error)) return 1;
    vmap_b = clCreateBuffer(context, CL_MEM_READ_WRITE | CL_MEM_USE_HOST_PTR,
                       sizeof(cl_uint) * num_virtual, vmap, &status);
    if (check_status(status, error)) return 1;
    adjs_b = clCreateBuffer(context, CL_MEM_READ_WRITE | CL_MEM_USE_HOST_PTR,
                       sizeof(cl_uint) * num_edges, adjs, &status);
    if (check_status(status, error)) return 1;
    /////////////////////////////////////////////////////////////////
	// Load CL file, build CL program object, create CL kernel object
	/////////////////////////////////////////////////////////////////
    const char * filename  = "brandes_kern.cl";
    std::string  sourceStr = convertToString(filename);
    const char * source    = sourceStr.c_str();
    size_t sourceSize[]    = { strlen(source) };

    program = clCreateProgramWithSource(context, 1, &source, sourceSize, &status);
    error = "Error: Loading Binary into cl_program \
	        (clCreateProgramWithBinary)\n";
    if (check_status(status, error)) return 1;
    
    /* create a cl program executable for all the devices specified */
    status = clBuildProgram(program, 1, devices, NULL, NULL, NULL);
    error = "Error: Building Program (clBuildProgram)\n";
    if (check_status(status, error)) return 1;

    /* get a kernel object handle for a kernel with the given name */
    init_array = clCreateKernel(program, "init_array", &status); 
    if (check_kern(status)) return 1;

    forward = clCreateKernel(program, "forward", &status); 
    if (check_kern(status)) return 1;
   
    middle = clCreateKernel(program, "middle", &status); 
    if (check_kern(status)) return 1;
	
    backward = clCreateKernel(program, "backward", &status); 
    if (check_kern(status)) return 1;
    
    final = clCreateKernel(program, "final", &status); 
    if (check_kern(status)) return 1;
    return 0;
}

cl_uint check_status(cl_int status, std::string text)
{
    if(status != CL_SUCCESS) 
	{ 
        std::cout << status << endl;
		std::cout << text;
		return 1; 
	}
    return 0;
}


cl_uint set_all_args()
{

    //*************************************************************************
    //               Setting args to init_array kernel
    //************************************************************************
    if (set_arg(init_array, 0, sizeof(cl_mem), sigma)) return 1;
    if (set_arg(init_array, 1, sizeof(cl_mem), d)) return 1;
    if (set_arg_int(init_array, 2, sizeof(cl_uint), num_vertex)) return 1;
    
    //*************************************************************************
    //               Setting args to for kernel
    //*************************************************************************
    if (set_arg(forward, 0, sizeof(cl_mem), sigma)) return 1;
    if (set_arg(forward, 1, sizeof(cl_mem), d)) return 1;
    if (set_arg(forward, 2, sizeof(cl_mem), vptrs_b)) return 1;
    if (set_arg(forward, 3, sizeof(cl_mem), vmap_b)) return 1;
    if (set_arg(forward, 4, sizeof(cl_mem), adjs_b)) return 1;
    if (set_arg_int(forward, 5, sizeof(cl_uint), num_virtual)) return 1;
    
    if (set_arg(forward, 6, sizeof(cl_mem), cont_b)) return 1;
    //*************************************************************************
    //               Setting args to middle kernel
    //*************************************************************************
    if (set_arg(middle, 0, sizeof(cl_mem), sigma)) return 1;
    if (set_arg(middle, 1, sizeof(cl_mem), delta_b)) return 1;
    if (set_arg(middle, 2, sizeof(cl_mem), d)) return 1;
    if (set_arg_int(middle, 3, sizeof(cl_uint), num_vertex)) return 1;
    
    if (set_arg(backward, 0, sizeof(cl_mem), delta_b)) return 1;
    if (set_arg(backward, 1, sizeof(cl_mem), vptrs_b)) return 1;
    if (set_arg(backward, 2, sizeof(cl_mem), vmap_b)) return 1;
    if (set_arg(backward, 3, sizeof(cl_mem), adjs_b)) return 1;
    if (set_arg(backward, 4, sizeof(cl_mem), d)) return 1;
    if (set_arg_int(backward, 5, sizeof(cl_uint), num_virtual)) return 1;
    //if (set_arg(forward, 1, sizeof(cl_mem), d)) return 1;
    //if (set_arg(forward, 2, sizeof(cl_mem), vptrs_b)) return 1;
   // if (set_arg(forward, 3, sizeof(cl_mem), vmap_b)) return 1;
    
    //*************************************************************************
    //               Setting args to final kernel
    //*************************************************************************
    if (set_arg(final, 0, sizeof(cl_mem), C_b)) return 1;
    if (set_arg(final, 1, sizeof(cl_mem), delta_b)) return 1;
    if (set_arg(final, 2, sizeof(cl_mem), sigma)) return 1;
    if (set_arg(final, 3, sizeof(cl_mem), d)) return 1;
    if (set_arg_int(final, 5, sizeof(cl_uint), num_vertex)) return 1;

    return 0;


}


//*****************************************************************************
//                       		  Run the CL kernel
//*****************************************************************************
int runCLKernels(void)
{
    cl_int   status;
	cl_uint maxDims;
    cl_event events[2];
    size_t globalThreads[1];
    size_t localThreads[1];
	size_t maxWorkGroupSize;
	size_t maxWorkItemSizes[3];
    cl_uint addressBits;

    globalThreads[0] = num_virtual - num_virtual % 64 + 64; //num_virtual; 
    localThreads[0]  = 64;

    if (dev_info(CL_DEVICE_MAX_WORK_GROUP_SIZE, sizeof(size_t), (void*)&maxWorkGroupSize)) return 1;
    if (dev_info(CL_DEVICE_MAX_WORK_ITEM_DIMENSIONS, sizeof(cl_uint), (void*)&maxDims)) return 1;
    if (dev_info(CL_DEVICE_MAX_WORK_ITEM_SIZES, sizeof(size_t)*(num_vertex),(void*)maxWorkItemSizes)) return 1;
    if (dev_info(CL_DEVICE_MAX_WORK_ITEM_SIZES, sizeof(size_t)*(num_vertex),(void*)maxWorkItemSizes)) return 1;
    if (dev_info(CL_DEVICE_ADDRESS_BITS, sizeof(cl_uint), &addressBits)) return 1;
    
    if (set_all_args()) return 1; 
    //*************************************************************************
    //               Perform algorithm
    //*************************************************************************
    for (cl_uint akt = 0; akt < num_vertex; ++akt) {

        if (set_arg_int(init_array, 3, sizeof(cl_uint), akt)) return 1;

        if (enqueue_kernel(commandQueue, init_array, 1, NULL,                         
                     globalThreads, localThreads, 0, NULL, &events[0])) return 1;
        /* wait for the kernel call to finish execution */
        if (wait_ev(1, &events[0])) return 1;
        if (release_ev(events[0])) return 1;

        *cont = 1;
        cl_uint l = 0;
        while (*cont) {
            *cont = 0; 
        //    printf("cont %d %d\n", *cont, l);
            status = clEnqueueWriteBuffer(commandQueue,                                                   
                        cont_b, CL_TRUE, 0, sizeof(cl_uint), cont, 0, NULL, &events[0]);
                                                                                        
            if(status != CL_SUCCESS)                                                    
            {                                                                           
                std::cout <<                                                            
                    "Error: clEnqueueReadBuffer failed.(clEnqueueReadBuffer)\n";                                          
                                                                                        
                return 1;                                                               
            }                                                                           
            if (wait_ev(1, &events[0])) return 1;
            if (release_ev(events[0])) return 1;
            
	    if (set_arg_int(forward, 7, sizeof(cl_uint), l)) return 1;
            if (enqueue_kernel(commandQueue, forward, 1, NULL,                         
                         globalThreads, localThreads, 0, NULL, &events[0])) return 1;
            /* wait for the kernel call to finish execution */
            if (wait_ev(1, &events[0])) return 1;
            if (release_ev(events[0])) return 1;
            status = clEnqueueReadBuffer(commandQueue,                                                   
                        cont_b, CL_TRUE, 0, sizeof(cl_uint), cont, 0, NULL, &events[0]);
                                                                                        
            if(status != CL_SUCCESS)                                                    
            {                                                                           
                std::cout <<                                                            
                    "Error: clEnqueueReadBuffer failed.(clEnqueueReadBuffer)\n";                                          
                                                                                        
                return 1;                                                               
            }                                                                           

            if (wait_ev(1, &events[0])) return 1;
            if (release_ev(events[0])) return 1;
            l++;
        }

        if (enqueue_kernel(commandQueue, middle, 1, NULL,                         
                     globalThreads, localThreads, 0, NULL, &events[0])) return 1;
        /* wait for the kernel call to finish execution */
        if (wait_ev(1, &events[0])) return 1;
        if (release_ev(events[0])) return 1;
       
        while (l > 1) {
            l--;
            if (set_arg_int(backward, 6, sizeof(cl_uint), l)) return 1;
            if (enqueue_kernel(commandQueue, backward, 1, NULL,                         
                         globalThreads, localThreads, 0, NULL, &events[0])) return 1;
            /* wait for the kernel call to finish execution */
            if (wait_ev(1, &events[0])) return 1;
            if (release_ev(events[0])) return 1;

        } 
        if (set_arg_int(final, 4, sizeof(cl_uint), akt)) return 1;
        if (enqueue_kernel(commandQueue, final, 1, NULL,                         
                     globalThreads, localThreads, 0, NULL, &events[0])) return 1;
        if (wait_ev(1, &events[0])) return 1;
        if (release_ev(events[0])) return 1;
    /* Enqueue readBuffer*/                                                     
    }

    status = clEnqueueReadBuffer(                                               
                commandQueue,                                                   
                C_b,                                                   
                CL_TRUE,                                                        
                0,                                                              
                num_vertex * sizeof(cl_uint),                                        
                C,                                                         
                0,                                                              
                NULL,                                                           
                &events[0]);                                                    
                                                                                
    if(status != CL_SUCCESS)                                                    
    {                                                                           
        std::cout <<                                                            
            "Error: clEnqueueReadBuffer failed.(clEnqueueReadBuffer)\n";                                          
                                                                                
        return 1;                                                               
    }                                                                           

        if (wait_ev(1, &events[0])) return 1;
        if (release_ev(events[0])) return 1;
    for(uint i = 0; i < num_vertex; i++){
        printf("%f\n", C[i]);
    }
	return 0;
}



int main(int argc, char * argv[])
{
    num_vertex = readData(argv[1]) + 1;
	if(initializeHost()==1) return 1;
    if(initializeCL()==1) return 1;

    if(runCLKernels()==1) return 1;

    if(cleanupCL()==1)
		return 1;
    cleanupHost();
    return 0;
}




/*
 * \brief Release OpenCL resources (Context, Memory etc.) 
 */
int cleanupCL(void)
{
    cl_int status;

    status = clReleaseProgram(program);
    if(status != CL_SUCCESS)
	{
		std::cout<<"Error: In clReleaseProgram\n";
		return 1; 
	}
    status = clReleaseMemObject(sigma);
    if(status != CL_SUCCESS)
	{
		std::cout<<"Error: In clReleaseMemObject (inputBuffer)\n";
		return 1; 
	}
    status = clReleaseMemObject(d);
    if(status != CL_SUCCESS)
	{
		std::cout<<"Error: In clReleaseMemObject (inputBuffer)\n";
		return 1; 
	}
    status = clReleaseMemObject(delta_b);
    if(status != CL_SUCCESS)
	{
		std::cout<<"Error: In clReleaseMemObject (inputBuffer)\n";
		return 1; 
	}
    status = clReleaseMemObject(C_b);
    if(status != CL_SUCCESS)
	{
		std::cout<<"Error: In clReleaseMemObject (inputBuffer)\n";
		return 1; 
	}
    status = clReleaseMemObject(cont_b);
    if(status != CL_SUCCESS)
	{
		std::cout<<"Error: In clReleaseMemObject (inputBuffer)\n";
		return 1; 
	}
    status = clReleaseCommandQueue(commandQueue);
    if(status != CL_SUCCESS)
	{
		std::cout<<"Error: In clReleaseCommandQueue\n";
		return 1;
	}
    status = clReleaseContext(context);
    if(status != CL_SUCCESS)
	{
		std::cout<<"Error: In clReleaseContext\n";
		return 1;
	}

	return 0;
}


/* 
 * \brief Releases program's resources 
 */
void cleanupHost(void)
{
    if(sig != NULL)
    {
        free(sig);
        input = NULL;
    }
    if(dd != NULL)
    {
        free(dd);
        input = NULL;
    }
    if(delta != NULL)
    {
        free(delta);
        input = NULL;
    }
    if(C != NULL)
    {
        free(C);
        input = NULL;
    }
	if(cont != NULL)
	{
		free(cont);
		output = NULL;
	}
    if(devices != NULL)
    {
        free(devices);
        devices = NULL;
    }
}

/*
 * Converts the contents of a file into a string
 */
std::string convertToString(const char *filename)
{
	size_t size;
	char*  str;
	std::string s;

	std::fstream f(filename, (std::fstream::in | std::fstream::binary));

	if(f.is_open())
	{
		size_t fileSize;
		f.seekg(0, std::fstream::end);
		size = fileSize = (size_t)f.tellg();
		f.seekg(0, std::fstream::beg);

		str = new char[size+1];
		if(!str)
		{
			f.close();
			return NULL;
		}

		f.read(str, fileSize);
		f.close();
		str[size] = '\0';
	
		s = str;
		delete[] str;
		return s;
	}
	else
	{
		std::cout << "\nFile containg the kernel code(\".cl\") not found. Please copy the required file in the folder containg the executable.\n";
		exit(1);
	}
	return NULL;
}






void print_vec(std::vector<int> array) 
{
    FOREACH(elt, array)
        cout << *elt << " ";
    cout << endl;
}

void print_graph() 
{
	FOREACH(elt,  graph) {
		cout << "Klucz :" << elt->first;
		cout << " Wektor :";
		for (cl_uint i = 0; i < elt->second.size(); i++){
  			cout << elt->second[i];
			cout << " ";  
		}
		cout << endl << endl;
	}
}

void print_array(cl_uint* array, int num_virtual)
{
    REP(i, num_virtual) printf("%d ", array[i]);
    printf("\n");
}

int readData(char* fileName) 
{
    int a, b, maxVertex = 0;
    FILE* f = fopen(fileName, "r");
    num_edges = 0;
    while (fscanf(f, "%d %d", &a, &b) != EOF) {
        num_edges++;
        graph[a].push_back(b);
        graph[b].push_back(a);
        maxVertex = max(maxVertex, max(a, b));
    }
    num_edges *= 2;
    fseek(f, 0, SEEK_SET);
    
    //print_graph();
    int num_vertex = maxVertex + 1;
   
    num_neigh.resize(num_vertex);
    FOREACH(elt, graph)
        num_neigh[elt->first] = elt->second.size();      
    //print_vec(num_neigh);

    // number of virtual verticies
    num_virtual = 0;
    REP(i, num_vertex) {
        if (num_neigh[i] == 0) num_virtual++;
        num_virtual += num_neigh[i]/MAX_NEIGH;
        if (num_neigh[i] % MAX_NEIGH != 0) num_virtual++;
    }
    vmap = (cl_uint *) calloc(num_virtual, sizeof(int));
    vptrs = (cl_uint *) calloc(num_virtual + 1, sizeof(cl_uint));
    adjs = (cl_uint *) calloc(num_edges, sizeof(int));
    // wypelnianie tablic  adjs  
    int e = 0;
    FOREACH(elt, graph) {
        FOREACH(i, elt->second) {
            adjs[e] = *i;
            e++;
        }
    }
      
    // wypelnianie tablicy  vmap i vptrs
    int current = 0;
    int ptrs_i = 0;
    REP(i, num_vertex) {
        int ile = 0;
        if (num_neigh[i] == 0) ile = 1;
        else {
            ile = (num_neigh[i] -1) /MAX_NEIGH + 1;
        }
        // printf("ile: %d\n", ile);
        REP(k, ile) {
            //printf("k: %d\n", k);
            vmap[current] = i;
            vptrs[current] = ptrs_i;
            if (k + 1 == ile) ptrs_i += (num_neigh[i]-1) % MAX_NEIGH + 1;
            else
                ptrs_i += MAX_NEIGH;
            current++;
        }
    }
    vptrs[current] = num_edges;
    
    fclose(f);
    return maxVertex;
}

cl_uint check_kern(cl_uint status)
{
    if(status != CL_SUCCESS) 
	{  
		std::cout<<"Error: Creating Kernel from program. (clCreateKernel)\n";
		return 1;
	}
    return 0;
}


cl_uint check_float(cl_float* pointer)
{
	if(pointer == NULL)
	{
		std::cout<<"Error: Failed to allocate input memory on host\n";
		return 1; 
	}
    return 0;
}

cl_uint check(cl_uint* pointer)
{
	if(pointer == NULL)
	{
		std::cout<<"Error: Failed to allocate input memory on host\n";
		return 1; 
	}
    return 0;
}


cl_int set_arg (cl_kernel kernel, cl_uint ind, size_t size, const void *value) {
    cl_int status;                                                              
    status = clSetKernelArg(kernel, ind, size, (void *)&value);                 
        if(status != CL_SUCCESS)                                                    
        {                                                                           
            printf("%d\n", status);                                                    
            if (DEBUG) printf("%s\n", "BAUAUAUAUAUUAUUAUAHAHAHAH");                 
            std::cout<< "Error: Setting kernel argument. (input)\n";                
            return 1;                                                               
        }                                                                           
     return 0;                                                                   
}


cl_int dev_info(cl_device_info param_name, size_t param_value_size, void *param_value) {
    cl_int status;                                                              
    status = clGetDeviceInfo(devices[0], param_name, param_value_size, param_value, NULL);  
    if(status != CL_SUCCESS)                                                    
    {                                                                           
        std::cout<<"Error: Getting Device Info. (clGetDeviceInfo)\n";           
        return 1;                                                               
    }                                                                           
    return 0;                                                                   
}


cl_int set_arg_int (cl_kernel kernel, cl_uint ind, size_t size, cl_uint  value) {
    cl_int status;                                                              
    status = clSetKernelArg(kernel, ind, size, (void *)&value);                 
        if(status != CL_SUCCESS)                                                    
        {                                                                           
            printf("%d\n", ind);                                                    
            if (DEBUG) printf("%s\n", "BAUAUAUAUAUUAUUAUAHAHAHAH");                 
            std::cout<< "Error: Setting kernel argument. (input)\n";                
            return 1;                                                               
        }                                                                           
     return 0;                                                                   
}

//******************************************************************************
//      Enqueue a kernel run call.
//*****************************************************************************/

cl_int enqueue_kernel ( cl_command_queue command_queue,
    cl_kernel kernel,
    cl_uint work_dim,
    const size_t *global_work_offset,
    const size_t *global_work_size,
    const size_t *local_work_size,
    cl_uint num_events_in_wait_list,
    const cl_event *event_wait_list,
    cl_event *event) {
    cl_int status;
    status = clEnqueueNDRangeKernel(commandQueue, kernel, work_dim, global_work_offset,
                 global_work_size, local_work_size, num_events_in_wait_list, event_wait_list, event);

    if(status != CL_SUCCESS) 
    { 
        std::cout<<
            "Error: Enqueueing kernel onto command queue. \
            (clEnqueueNDRangeKernel)\n";
        return 1;
    }
    return 0;
}


cl_int wait_ev(cl_uint num_events, const cl_event *event_list)
{
    cl_uint status;
    status = clWaitForEvents(num_events, event_list);
    if(status != CL_SUCCESS) 
	{ 
	  	std::cout<<
	   	    "Error: Waiting for kernel run to finish. \
	   		(clWaitForEvents)\n";
	   	return 1;
	}
    return 0;
}


cl_int release_ev (cl_event event)
{
    cl_uint status;
    status = clReleaseEvent(event);
    if(status != CL_SUCCESS) 
	{ 
	   	std::cout<<
	   	    "Error: Release event object. \
	   		(clReleaseEvent)\n";
	  	return 1;
	}
    return 0;
}



/*
 * \brief Print no more than 256 elements of the given array.
 *
 *        Print Array name followed by elements.
 */
void print1DArray(
		 const std::string arrayName, 
         const unsigned int * arrayData, 
         const unsigned int length)
{
    cl_uint i;
    cl_uint numElementsToPrint = (256 < length) ? 256 : length;

    std::cout << std::endl;
    std::cout << arrayName << ":" << std::endl;
    for(i = 0; i < numElementsToPrint; ++i)
    {
        std::cout << arrayData[i] << " ";
    }
    std::cout << std::endl;

}

void verify()
{
    bool passed = true;
    for(unsigned int i = 0; i < width; ++i)
        if(input[i] * multiplier != output[i])
            passed = false;

    if(passed == true)
        std::cout << "Passed!\n";
    else
        std::cout << "Failed!\n";
}


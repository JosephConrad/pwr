// Konrad Lisiecki PWIR 2014

//*****************************************************************************
//          Atomic_add dla floatow - zrodlo:
// http://simpleopencl.blogspot.com/2013/05/atomic-operations-and-floats-in-opencl.html
//*****************************************************************************
void atomic_add_global(volatile global float *source, const float operand) {
    union {
        unsigned int intVal;
        float floatVal;
    } newVal;
    union {
        unsigned int intVal;
        float floatVal;
    } prevVal;
 
    do {
        prevVal.floatVal = *source;
        newVal.floatVal = prevVal.floatVal + operand;
    } while (atomic_cmpxchg((volatile global unsigned int *)source, prevVal.intVal, newVal.intVal) != prevVal.intVal);
}



//*****************************************************************************
//                      Kernel init
//*****************************************************************************
__kernel void init_array(  __global int* sigma,
                           __global int* d,
                           const unsigned int num_vertex,
                           const unsigned int l)
{
    uint v = get_global_id(0);
    int i; 
    if (v < num_vertex  && v == l) {
        sigma[v] = 1;
        d[v] = 0;
    } else if (v < num_vertex) {
        sigma[v] = 0; 
        d[v] = -1;
    }
    barrier(CLK_LOCAL_MEM_FENCE);
}



//*****************************************************************************
//                      Kernel forward 
//*****************************************************************************
__kernel void forward(  __global int* sigma,
                    __global int* d,
                    __global int* vptrs,
                    __global int* vmap,
                    __global int* adjs,
                    const unsigned int num_virtual,
                    __global int* cont,
                    const unsigned int l)
{
     uint tid = get_global_id(0); 
     barrier(CLK_LOCAL_MEM_FENCE);
     if (tid < num_virtual) 
     {
     	uint u = vmap[tid];
	if ( d[u] == l)
     	{
	    uint range = vptrs[tid+1];
            for (int j = vptrs[tid]; j < range; j++){

                 int v = adjs[j];
                 if (d[v] == -1) {
                     d[v] = l + 1; 
                     *cont = 1;
                     //*cont = l + 1;
                 }
                 if (d[v] == (l + 1)) atomic_add(&sigma[v], sigma[u]);
	    }
         }
     }
}


//*****************************************************************************
//                      Kernel middle 
//*****************************************************************************
__kernel void middle(__global int* sigma,                                       
                     __global float* delta,
                     __global int* d,                                      
                     unsigned int num_vertex)                               
{                                                                               
    int v = get_global_id(0);                                                  
    if (v < num_vertex && d[v] != -1)                                          
        delta[v] = (float) (1.00f / sigma[v]);                                     
}


//*****************************************************************************
//                      Kernel backward 
//*****************************************************************************
__kernel void backward(__global float* delta,
                    __global int* vptrs,
                    __global int* vmap,
                    __global int* adjs,
                    __global int* d,
                    const unsigned int num_virtual,
                    const unsigned int l)
{
     uint tid = get_global_id(0); 
     if (tid < num_virtual)
     {
     	 uint u = vmap[tid];
 	 if (d[u] == l) {
             float sum = 0;
	     uint range = vptrs[tid+1];
             for (int j = vptrs[tid]; j < range; j++){
                 int v = adjs[j];
                 if (d[v] == l+1) sum += delta[v];
             }
             atomic_add_global(&delta[u], sum);
	 }
     }
}



//*****************************************************************************
//                      Kernel final 
//*****************************************************************************
__kernel void final(__global float* C,
                    __global float* delta,
                    __global int* sigma,
                    __global int* d,
                    unsigned int akt,
                    unsigned int num_vertex)
{
    int v = get_global_id(0);
        
    if (v != akt && v < num_vertex && d[v] != -1) {
        C[v] = C[v] + (delta[v] * sigma[v] -1);
    }
}

//*****************************************************************************
//                      Kernel init
//*****************************************************************************
__kernel void templateKernel(__global  unsigned int * output,
                             __global  unsigned int * input,
                             const     unsigned int multiplier)
{
    uint tid = get_global_id(0);
    output[tid] = input[tid] * multiplier;
}


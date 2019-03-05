#include <stdio.h>
#include <math.h>
#include "const.h"
#include "defs.h"
#include "extern.h"
#include "function.h"
#include <limits.h>

namespace voronoi{
    // A utility function to create a new adjacency list node 
    struct AdjListNode* newAdjListNode(int dest, int lineseg_idx, int weight) 
    { 
        struct AdjListNode* newNode = 
         (struct AdjListNode*) myalloc(sizeof(struct AdjListNode)); 
        newNode->dest = dest; 
        newNode->weight = weight;
        newNode->lineseg_idx = lineseg_idx;
        newNode->next = NULL; 
        return newNode; 
    } 

    // A utility function that creates a graph of V vertices 
    struct Graph* createGraph(int V) 
    { 
        struct Graph* graph =  (struct Graph*) myalloc(sizeof(struct Graph)); 
        graph->V = V; 
      
        // Create an array of adjacency lists.  Size of  
        // array will be V 
        graph->array =  
          (struct AdjList*) myalloc(V * sizeof(struct AdjList)); 
      
        // Initialize each adjacency list as empty by  
        // making head as NULL 
        int i; 
        for (i = 0; i < V; ++i) 
            graph->array[i].head = NULL; 
      
        return graph; 
    }

    // A utility function to create a new Min Heap Node 
    struct MinHeapNode* newMinHeapNode(int v, int dist) 
    { 
        struct MinHeapNode* minHeapNode = 
               (struct MinHeapNode*) myalloc(sizeof(struct MinHeapNode)); 
        minHeapNode->v = v; 
        minHeapNode->dist = dist; 
        return minHeapNode; 
    } 
      
    // A utility function to create a Min Heap 
    struct MinHeap* createMinHeap(int capacity) 
    { 
        struct MinHeap* minHeap = 
             (struct MinHeap*) myalloc(sizeof(struct MinHeap)); 
        minHeap->pos = (int *)myalloc(capacity * sizeof(int)); 
        minHeap->size = 0; 
        minHeap->capacity = capacity; 
        minHeap->array = 
             (struct MinHeapNode**) myalloc(capacity * sizeof(struct MinHeapNode*)); 
        return minHeap; 
    } 
      

    // A utility function to swap two nodes of min heap. Needed for min heapify 
    void swapMinHeapNode(struct MinHeapNode** a, struct MinHeapNode** b) 
    { 
        struct MinHeapNode* t = *a; 
        *a = *b; 
        *b = t; 
    } 
      
    // A standard function to heapify at given idx 
    // This function also updates position of nodes when they are swapped. 
    // Position is needed for decreaseKey() 
    void minHeapify(struct MinHeap* minHeap, int idx) 
    { 
        int smallest, left, right; 
        smallest = idx; 
        left = 2 * idx + 1; 
        right = 2 * idx + 2; 
      
        if (left < minHeap->size && 
            minHeap->array[left]->dist < minHeap->array[smallest]->dist ) 
          smallest = left; 
      
        if (right < minHeap->size && 
            minHeap->array[right]->dist < minHeap->array[smallest]->dist ) 
          smallest = right; 
      
        if (smallest != idx) 
        { 
            // The nodes to be swapped in min heap 
            MinHeapNode *smallestNode = minHeap->array[smallest]; 
            MinHeapNode *idxNode = minHeap->array[idx]; 
      
            // Swap positions 
            minHeap->pos[smallestNode->v] = idx; 
            minHeap->pos[idxNode->v] = smallest; 
      
            // Swap nodes 
            swapMinHeapNode(&minHeap->array[smallest], &minHeap->array[idx]); 
      
            minHeapify(minHeap, smallest); 
        } 
    } 
      
    // A utility function to check if the given minHeap is ampty or not 
    int isEmpty(struct MinHeap* minHeap) 
    { 
        return minHeap->size == 0; 
    } 
      
    // Standard function to extract minimum node from heap 
    struct MinHeapNode* extractMin(struct MinHeap* minHeap) 
    { 
        if (isEmpty(minHeap)) 
            return NULL; 
      
        // Store the root node 
        struct MinHeapNode* root = minHeap->array[0]; 
      
        // Replace root node with last node 
        struct MinHeapNode* lastNode = minHeap->array[minHeap->size - 1]; 
        minHeap->array[0] = lastNode; 
      
        // Update position of last node 
        minHeap->pos[root->v] = minHeap->size-1; 
        minHeap->pos[lastNode->v] = 0; 
      
        // Reduce heap size and heapify root 
        --minHeap->size; 
        minHeapify(minHeap, 0); 
      
        return root; 
    } 
      
    // Function to decreasy dist value of a given vertex v. This function 
    // uses pos[] of min heap to get the current index of node in min heap 
    void decreaseKey(struct MinHeap* minHeap, int v, int dist) 
    { 
        // Get the index of v in  heap array 
        int i = minHeap->pos[v]; 
      
        // Get the node and update its dist value 
        minHeap->array[i]->dist = dist; 
      
        // Travel up while the complete tree is not hepified. 
        // This is a O(Logn) loop 
        while (i && minHeap->array[i]->dist < minHeap->array[(i - 1) / 2]->dist) 
        { 
            // Swap this node with its parent 
            minHeap->pos[minHeap->array[i]->v] = (i-1)/2; 
            minHeap->pos[minHeap->array[(i-1)/2]->v] = i; 
            swapMinHeapNode(&minHeap->array[i],  &minHeap->array[(i - 1) / 2]); 
      
            // move to parent index 
            i = (i - 1) / 2; 
        } 
    } 
      
    // A utility function to check if a given vertex 
    // 'v' is in min heap or not 
    bool isInMinHeap(struct MinHeap *minHeap, int v) 
    { 
        bool DEBUG = false;
        if(DEBUG) printf("[isInMinHeap] Start...\n");
        if(DEBUG) printf("[isInMinHeap] minHeap->pos[%d]...\n",v);
        if (minHeap->pos[v] < minHeap->size) 
            return true; 
        return false; 
    } 
      
    // A utility function used to print the solution 
    void printArr(int dist[], int n) 
    { 
        printf("Vertex   Distance from Source\n"); 
        for (int i = 0; i < n; ++i) 
            printf("%d \t\t %d\n", i, dist[i]); 
    } 

    // The main function that calulates distances of shortest paths from src to all 
    // vertices. It is a O(ELogV) function 
    void dijkstra(struct Graph* graph, int src, int tar, int lineseg_idx) 
    { 
        bool DEBUG = false;
        int V = graph->V;// Get the number of vertices in graph 
        int dist[V];      // dist values used to pick minimum weight edge in cut 
        int path[V];
        // minHeap represents set E 
        struct MinHeap* minHeap = createMinHeap(V); 
        
        // Initialize min heap with all vertices. dist value of all vertices  
        if(DEBUG) printf("[dijstra] START...\n");
        for (int v = 0; v < V; ++v) 
        { 
            dist[v] = INT_MAX; 
            minHeap->array[v] = newMinHeapNode(v, dist[v]); 
            minHeap->pos[v] = v; 
        } 
        if(DEBUG) printf("[dijstra] minHeap is initialized...\n");
        
        // Make dist value of src vertex as 0 so that it is extracted first 
        minHeap->array[src] = NULL;
        minHeap->array[src] = newMinHeapNode(src, dist[src]); 
        minHeap->pos[src]   = src; 
        dist[src] = 0; 
        path[src] = src;
        decreaseKey(minHeap, src, dist[src]); 
        // Initially size of min heap is equal to V 
        minHeap->size = V; 
        
        if(DEBUG) printf("[dijstra] src vertex is initialized...\n");

        // In the followin loop, min heap contains all nodes 
        // whose shortest distance is not yet finalized. 
        while (!isEmpty(minHeap)) 
        { 
            if(DEBUG) printf("[dijstra] outter while loop...\n");
            // Extract the vertex with minimum distance value 
            struct MinHeapNode* minHeapNode = extractMin(minHeap); 
            int u = minHeapNode->v; // Store the extracted vertex number 
            // Traverse through all adjacent vertices of u (the extracted 
            // vertex) and update their distance values 

            struct AdjListNode* pCrawl = graph->array[u].head; 
            while (pCrawl != NULL) 
            { 
                int v = pCrawl->dest; 
                if(DEBUG) printf("[dijstra] u:%d - v:%d ...\n",u,v);  
                // If shortest distance to v is not finalized yet, and distance to v 
                // through u is less than its previously calculated distance 
                if (isInMinHeap(minHeap, v) && dist[u] != INT_MAX &&  
                                              pCrawl->weight + dist[u] < dist[v]) 
                { 
                    if(DEBUG) printf("[dijstra] inner while loop...1\n");  
                    dist[v] = dist[u] + pCrawl->weight; 
                    //printf("v:%d ... u:%d\n",v,u);
                    path[v] = u;
                    // update distance value in min heap also 
                    decreaseKey(minHeap, v, dist[v]); 
                } 
                pCrawl = pCrawl->next; 
            } 
            //free(minHeapNode);
            //free(pCrawl);
        } 
        // print the calculated shortest distances 
        if(DEBUG) printf("[dijstra] shorest paths are found...\n");

        if(DEBUG) printArr(dist, V); 
        /*
        printf("\n\nPATH:\n");
        for (int q=0 ; q<V ; q++){
            printf("\t%d \t\t %d\n",q,path[q]);
        }
        */
        
        if(dist[tar]!=INT_MAX){
            assignZone(graph,path,V,src,tar,lineseg_idx);
            return;
        }
        else
            if(DEBUG) printf("From %d to %d is unreachable.\n",src,tar);
        
        
        /*
        for (int v = 0; v < V; ++v) 
            free(minHeap->array[v]); 
        */
        // Also might need to free minHeap->array[src] ... but it gives an error somehow...
        /*   
        free(minHeap->array);
        free(minHeap->pos); 
        free(minHeap);
        */
    } 
}

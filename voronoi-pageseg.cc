/*
  $Date: 1999/10/15 12:40:27 $
  $Revision: 1.1.1.1 $
  $Author: kise $
  main.c
  ¥á¥¤¥ó¥×¥í¥°¥é¥à
*/

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "defs.h"
#include "const.h"
#include "function.h"
#include <limits.h>


namespace voronoi{
#define LINE_C  192 // blue color in range 0-255
#define WIDTH   5
#define MY_V       4500

    BlackPixel 	*bpx;		/* Coordinates of black pixels and their labels */
    Shape       *shape;
    Neighborhood	*neighbor;	/* Characteristic quantity between adjacent connected components */
    LineSegment	*lineseg;	/* Coordinates and labels of start and end points */
    LineSegment *lineseg_edge;
    HashTable	*hashtable[M1+M2];
    /* Hash table for labels of adjacent connected components */
    EndPoint	*endp;		/* End point of line segment */

    NumPixel	BPnbr;		/* Number of black pixels */
    Label	        LABELnbr;	/* Number of connected components */
    unsigned int	NEIGHnbr;	/* Number of adjacent connected component sets */
    unsigned int	LINEnbr;	/* Number of line segments before removal Voronoi side */
    unsigned int    ZONEnbr;
    unsigned int	Enbr;		/* Number of connected component sets from which Voronoi sides are removed */
    long		SiteMax;	/* Maximum number of Voronoi points */

    int		noise_max = NOISE_MAX;	   /* Number of pixels of connected component to remove */
    int		sample_rate = SAMPLE_RATE; /* Sampling with boundary tracking */
					   /* Percentage */
    float		freq_rate = FREQ_RATE;
    int             Ta = Ta_CONST;
    int             Ts = Ts_CONST;
    unsigned int	sample_pix;	/* Pictures obtained by sampling */
    /* A prime number */
    unsigned int	point_edge;	/* Point Voronoi number of sides */
    unsigned int	edge_nbr;	/* Area after removal Voronoi side */
    /* Number of line segments */
    int             *area;       /* Label in the area of ​​the connected component attached */

    // Modification by Faisal Shafait
    // keep track of noise components to remove them
    // from the output image
    bool *noise_comp;
    unsigned int nconcomp_inc=50;
    unsigned int nconcomp_size=0;
    // End of Modification
    
#ifdef TIME
    float    b_s_time=0;
    float    v_time=0;
    float    e_time=0;
    float    o_time=0;
    clock_t		start, end;
#endif /* TIME */

    float	xmin, xmax, ymin, ymax, deltax, deltay;

    struct Site		*sites;
    int			nsites;
    int			siteidx;
    int			sqrt_nsites;
    int			nvertices;
    struct Freelist 	sfl;
    struct Site		*bottomsite;

    int 		nedges;
    struct Freelist 	efl;

    struct Freelist	hfl;
    struct	Halfedge	*ELleftend, *ELrightend;
    int 			ELhashsize;
    struct	Halfedge	**ELhash;

    int 			PQhashsize;
    struct	Halfedge 	*PQhash;
    int 			PQcount;
    int 			PQmin;

    /* ÄÉ²Ãµ¡Ç½ÍÑ */
    int    smwind = SMWIND;

    /* ÄÉ²ÃÊ¬ */
    char     output_points = NO;
    char     output_pvor = NO;
    char     output_avor = NO;
    char     display_parameters = NO;

    // A utility function to create a new Min Heap Node 
    struct MinHeapNode* newMinHeapNode(int v, int dist) 
    { 
        struct MinHeapNode* minHeapNode = 
               (struct MinHeapNode*) malloc(sizeof(struct MinHeapNode)); 
        minHeapNode->v = v; 
        minHeapNode->dist = dist; 
        return minHeapNode; 
    } 
      
    // A utility function to create a Min Heap 
    struct MinHeap* createMinHeap(int capacity) 
    { 
        struct MinHeap* minHeap = 
             (struct MinHeap*) malloc(sizeof(struct MinHeap)); 
        minHeap->pos = (int *)malloc(capacity * sizeof(int)); 
        minHeap->size = 0; 
        minHeap->capacity = capacity; 
        minHeap->array = 
             (struct MinHeapNode**) malloc(capacity * sizeof(struct MinHeapNode*)); 
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

    void assignZone(struct Graph* graph, int dist[], int path[], int n, int src, int tar, int lineseg_idx_src_tar)
    {
        printf("[assignZone] src:%d tar:%d\n",src,tar);
        //struct AdjListNode* printerCrawl = graph->array[parent].head; 

        int parent = tar;
        int lineseg_idx;
        struct AdjListNode* pCrawl;
        /*
        for(int i=0 ; i<graph->V ; i++)
        {
            printf("path: %d \t %d \n",i,path[i]);
        }
        */
        // tar-...
        while(path[parent]!=src)
        {
            pCrawl = graph->array[parent].head; 
            while(pCrawl)
            {
                if(pCrawl->dest==path[parent])
                {
                    lineseg_idx = pCrawl->lineseg_idx;
                    break;
                }
                pCrawl = pCrawl->next;
            }
            //lineseg[lineseg_idx].zone[lineseg[lineseg_idx].zone_idx++] = ZONEnbr;
            printf("lineseg[%d]: %d -> %d ... zone:%d\n",lineseg_idx,parent,path[parent],ZONEnbr);
            
            parent = path[parent];
        }
        // ...-src
        pCrawl = graph->array[parent].head; 
        while(pCrawl)
        {
            if(pCrawl->dest==path[parent])
            {
                lineseg_idx = pCrawl->lineseg_idx;
                break;
            }
            pCrawl = pCrawl->next;
        }
        //lineseg[lineseg_idx].zone[lineseg[lineseg_idx].zone_idx++] = ZONEnbr;
        printf("lineseg[%d]: %d -> %d ... zone:%d \n",lineseg_idx,parent,path[parent],ZONEnbr);
        // src-tar
        //lineseg[lineseg_idx_src_tar].zone[lineseg[lineseg_idx_src_tar].zone_idx++] = ZONEnbr;
        printf("lineseg[%d]: %d -> %d ... zone:%d \n",lineseg_idx_src_tar,src,tar,ZONEnbr);
        //ZONEnbr++;
    }

    // The main function that calulates distances of shortest paths from src to all 
    // vertices. It is a O(ELogV) function 
    void dijkstra(struct Graph* graph, int src, int tar, int lineseg_idx) 
    { 
        int V = graph->V;// Get the number of vertices in graph 
        int dist[V];      // dist values used to pick minimum weight edge in cut 
        int path[V];
        // minHeap represents set E 
        struct MinHeap* minHeap = createMinHeap(V); 
      
        // Initialize min heap with all vertices. dist value of all vertices  
        for (int v = 0; v < V; ++v) 
        { 
            dist[v] = INT_MAX; 
            minHeap->array[v] = newMinHeapNode(v, dist[v]); 
            minHeap->pos[v] = v; 
        } 
      
        // Make dist value of src vertex as 0 so that it is extracted first 
        minHeap->array[src] = newMinHeapNode(src, dist[src]); 
        minHeap->pos[src]   = src; 
        dist[src] = 0; 
        path[src] = src;
        decreaseKey(minHeap, src, dist[src]); 
      
        // Initially size of min heap is equal to V 
        minHeap->size = V; 
      
        // In the followin loop, min heap contains all nodes 
        // whose shortest distance is not yet finalized. 
        while (!isEmpty(minHeap)) 
        { 
            // Extract the vertex with minimum distance value 
            struct MinHeapNode* minHeapNode = extractMin(minHeap); 
            int u = minHeapNode->v; // Store the extracted vertex number 
      
            // Traverse through all adjacent vertices of u (the extracted 
            // vertex) and update their distance values 
            struct AdjListNode* pCrawl = graph->array[u].head; 
            while (pCrawl != NULL) 
            { 
                int v = pCrawl->dest; 
      
                // If shortest distance to v is not finalized yet, and distance to v 
                // through u is less than its previously calculated distance 
                if (isInMinHeap(minHeap, v) && dist[u] != INT_MAX &&  
                                              pCrawl->weight + dist[u] < dist[v]) 
                { 
                    dist[v] = dist[u] + pCrawl->weight; 
                    //printf("v:%d ... u:%d\n",v,u);
                    path[v] = u;
                    // update distance value in min heap also 
                    decreaseKey(minHeap, v, dist[v]); 
                } 
                pCrawl = pCrawl->next; 
            } 

        } 
        // print the calculated shortest distances 
        //printArr(dist, V); 
        if(dist[tar]!=INT_MAX)
            assignZone(graph,dist,path,MY_V,src,tar,lineseg_idx);
        else
            printf("From %d to %d is unreachable.\n",src,tar);
    } 

    // A utility function to create a new adjacency list node 
    struct AdjListNode* newAdjListNode(int dest, int lineseg_idx) 
    { 
        struct AdjListNode* newNode = 
         (struct AdjListNode*) malloc(sizeof(struct AdjListNode)); 
        newNode->dest = dest; 
        newNode->weight = 1;
        newNode->lineseg_idx = lineseg_idx;
        newNode->next = NULL; 
        return newNode; 
    } 
      
    // A utility function that creates a graph of V vertices 
    struct Graph* createGraph(int V) 
    { 
        struct Graph* graph =  (struct Graph*) malloc(sizeof(struct Graph)); 
        graph->V = V; 
      
        // Create an array of adjacency lists.  Size of  
        // array will be V 
        graph->array =  
          (struct AdjList*) malloc(V * sizeof(struct AdjList)); 
      
        // Initialize each adjacency list as empty by  
        // making head as NULL 
        int i; 
        for (i = 0; i < V; ++i) 
            graph->array[i].head = NULL; 
      
        return graph; 
    }

    // A utility function to print the adjacency list  
    // representation of graph 
    void printGraph(struct Graph* graph) 
    { 
        int v; 
        for (v = 0; v < graph->V; ++v) 
        { 
            struct AdjListNode* pCrawl = graph->array[v].head; 
            printf("\n Adjacency list of vertex %d\n head ", v); 
            while (pCrawl) 
            { 
                printf("-> %d", pCrawl->dest); 
                pCrawl = pCrawl->next; 
            } 
            printf("\n"); 
        } 
    } 

    // Adds an edge to an undirected graph 
    void addEdge(struct Graph* graph, int src, int dest, int lineseg_idx) 
    { 
        // Add an edge from src to dest.  A new node is  
        // added to the adjacency list of src.  The node 
        // is added at the begining 
        struct AdjListNode* newNode = newAdjListNode(dest,lineseg_idx); 
        newNode->next = graph->array[src].head; 
        graph->array[src].head = newNode; 
      
        // Since graph is undirected, add an edge from 
        // dest to src also 
        newNode = newAdjListNode(src,lineseg_idx); 
        newNode->next = graph->array[dest].head; 
        graph->array[dest].head = newNode; 
    } 

    void delEdge(struct Graph* graph, int src, int dest)
    {
        int DEBUG = 0;
        struct AdjListNode* pCrawl;
        struct AdjListNode* temp;
        // unlink src-dest
        pCrawl = graph->array[src].head;
        if(DEBUG){
            printf("[delEdge] src:%d dest:%d\n",src,dest);
            printf("[delEdge] \tpCrawl->next->dest:%d pCrawl->dest:%d\n",pCrawl->next->dest,pCrawl->dest);
        } 
        while (pCrawl) 
        { 
            if (DEBUG) printf("[delEdge] \tpCrawl: %d\n",pCrawl->dest);
            if(graph->array[src].head->dest==dest){
                // hmm... should I free something here?
                graph->array[src].head = graph->array[src].head->next;
                if (DEBUG) printf("[delEdge] \tdeleted.\n");
                break;
            }
            else if (pCrawl->next->dest==dest){
                pCrawl->next = pCrawl->next->next;
                temp = pCrawl->next;
                free(temp);
                if (DEBUG) printf("[delEdge] \tdeleted.\n");
                break;
            }
            else{
                if (DEBUG) printf("[delEdge] \tgetNext()\n");
                pCrawl = pCrawl->next; 
            }
                
        } 
    }

    // A utility function to find the vertex with minimum distance value, from 
    // the set of vertices not yet included in shortest path tree 
    int minDistance(int dist[], bool sptSet[]) 
    { 
        // Initialize min value 
        int min = INT_MAX, min_index; 

        for (int v = 0; v < MY_V; v++) 
            if (sptSet[v] == false && dist[v] <= min) 
                min = dist[v], min_index = v; 

        return min_index; 
    } 
       
    // A utility function to print the constructed distance array 
    void printSolution(int dist[], int path[], int n) 
    { 
        printf("Vertex   Distance from Source\n"); 
        for (int i = 0; i < MY_V; i++) 
            printf("%d \t\t %d\n", i, dist[i]); 
    }
    
    
    /*
    // Function that implements Dijkstra's single source shortest path algorithm 
    // for a graph represented using adjacency matrix representation 
    void dijkstra(unsigned int graph[MY_V][MY_V][2], int src, int tar) 
    { 
        int dist[MY_V];     // The output array.  dist[i] will hold the shortest 
                          // distance from src to i 
        int path[MY_V],path_idx=0;
       
        bool sptSet[MY_V]; // sptSet[i] will be true if vertex i is included in shortest 
                        // path tree or shortest distance from src to i is finalized 
       
        // Initialize all distances as INFINITE and stpSet[] as false 
        for (int i = 0; i < MY_V; i++) 
            dist[i] = INT_MAX, sptSet[i] = false; 
       
        // Distance of source vertex from itself is always 0 
        dist[src] = 0; 
        path[src] = src;

        // Find shortest path for all vertices 
        for (int count = 0; count < MY_V-1; count++) 
        { 
            // Pick the minimum distance vertex from the set of vertices not 
            // yet processed. u is always equal to src in the first iteration. 
            int u = minDistance(dist, sptSet); 

            // Mark the picked vertex as processed 
            sptSet[u] = true; 

            // Update dist value of the adjacent vertices of the picked vertex. 
            for (int v = 0; v < MY_V; v++) 
            {
                // Update dist[v] only if is not in sptSet, there is an edge from  
                // u to v, and total weight of path from src to  v through u is  
                // smaller than current value of dist[v] 
                if (!sptSet[v] && graph[u][v][0] && dist[u] != INT_MAX  
                                           && dist[u]+graph[u][v][0] < dist[v]) 
                {
                    dist[v] = dist[u] + graph[u][v][0]; 
                    path[v] = u;
                }
            }
            path_idx++;
        } 
        // print the constructed distance array 
        
        printf("PATH:\n");
        for(int i=0 ; i<V ; i++)
        {
            printf("%d \t %d\n",i,path[i]);
        }
        
        assignZone(graph,dist,path,MY_V,src,tar);
        //printSolution(dist,path,V); 
    } 
    */

    int compare_struct_x(const void *s1, const void *s2)
    {
        struct Site *_s1 = (struct Site *)s1;
        struct Site *_s2 = (struct Site *)s2;

        /*
        // sort by x coordinate
        if(xory=='x')
            return _s1->coord.x - _s2->coord.x;
        else
            return _s1->coord.y - _s2->coord.y;
        */
        return _s1->coord.x - _s2->coord.x;
    }
    int compare_struct_y(const void *s1, const void *s2)
    {
        struct Site *_s1 = (struct Site *)s1;
        struct Site *_s2 = (struct Site *)s2;

        /*
        // sort by x coordinate
        if(xory=='x')
            return _s1->coord.x - _s2->coord.x;
        else
            return _s1->coord.y - _s2->coord.y;
        */
        return _s1->coord.y - _s2->coord.y;
    }

    void voronoi_pageseg(LineSegment **mlineseg, 
                         unsigned int *nlines,
                         ImageData *imgd1) {

        point_edge = 0;
        edge_nbr = 0;

        BPnbr = LABELnbr = NEIGHnbr = LINEnbr = Enbr = SiteMax = 0;

        /* displaying parameters */
        if(display_parameters == YES)
            dparam();

        /* Set 1 pixels surrounding image to 0 */
        frame(imgd1,1,0);

        /* ¹õ²èÁÇbpx ¤ÎÎÎ°è³ÎÊÝ */
        bpx=(BlackPixel *)myalloc(sizeof(BlackPixel)* INITPIXEL);

        shape=(Shape * )myalloc(sizeof(Shape)* INITPIXEL);

        /* Site ·¿sites ¤ÎÎÎ°è³ÎÊÝ */
        sites = (struct Site *) myalloc(SITE_BOX*sizeof *sites);
    
        /* ÆþÎÏ²èÁü¤òSite ·¿¤ËÊÑ´¹ */
    
        fprintf(stderr,"Transforming Image to Site...\n");
#ifdef TIME
        start = clock();
#endif
        img_to_site(imgd1);
#ifdef TIME
        end = clock();
        b_s_time = (float)((end-start)/((float)CLOCKS_PER_SEC));
#endif
        fprintf(stderr,"done\n");

        /* area[ln] ¤ÎÎÎ°è³ÎÊÝ */
        area=(int *)myalloc(sizeof(int)*LABELnbr);

        /* area[ln] ¤ÎÃÍ¤ò½é´ü²½ */
        for(int i=0;i<LABELnbr;i++) area[i]=0;

        /* area[ln], set the value */
        for(int i=0;i<BPnbr;i++) area[bpx[i].label]++;

        for(int i=0;i<BPnbr;i++){
            shape[bpx[i].label].x_min=10000;
            shape[bpx[i].label].x_max=0;
            shape[bpx[i].label].y_min=10000;
            shape[bpx[i].label].y_max=0;
            //shape[bpx[i].label].conf={0.0};
            shape[bpx[i].label].conf_idx=0;
        }

        /* 

        shape [ [label:0, x_min:?, x_max:?, y_min:?, y_max:?],
                [label:1, x_min:?, x_max:?, y_min:?, y_max:?],
                [label:2, x_min:?, x_max:?, y_min:?, y_max:?],
                ...
                [label:n, x_min:?, x_max:?, y_min:?, y_max:?]]

        */
        
        for(int i=0;i<BPnbr;i++){
            if(shape[bpx[i].label].x_min > bpx[i].xax) shape[bpx[i].label].x_min=bpx[i].xax;
            if(shape[bpx[i].label].x_max < bpx[i].xax) shape[bpx[i].label].x_max=bpx[i].xax;
            if(shape[bpx[i].label].y_min > bpx[i].yax) shape[bpx[i].label].y_min=bpx[i].yax;
            if(shape[bpx[i].label].y_max < bpx[i].yax) shape[bpx[i].label].y_max=bpx[i].yax;
        }
        /*
        for(i=0;i<LABELnbr;i++){
            printf("\tx_min:%d x_max:%d y_min:%d y_max:%d\n",shape[i].x_min,shape[i].x_max,shape[i].y_min,shape[i].y_max);
        }
        */
        
        /* bpx ¤ÎÎÎ°è²òÊü */
        //        free(bpx);
    
        /* ÎÙÀÜÏ¢·ëÀ®Ê¬´Ö¤ÎÆÃÄ§ÎÌneighbor ¤ÎÎÎ°è³ÎÊÝ */
        neighbor = (Neighborhood *)myalloc(sizeof(Neighborhood)* INITNEIGHBOR);

        /* ÀþÊ¬lineseg ¤ÎÎÎ°è³ÎÊÝ */
        lineseg = (LineSegment *)myalloc(sizeof(LineSegment)* INITLINE);

        /* ¥Ï¥Ã¥·¥åÉ½¤ò½é´ü²½
           initialization of hash tables */
        init_hash();

        /* ¥¨¥ê¥¢Voronoi ¿ÞºîÀ® 
           constructing the area Voronoi diagram */
    
        fprintf(stderr,"Constructing area Voronoi diagram...\n");
#ifdef TIME
        start = clock();
#endif
        voronoi(imgd1->imax, imgd1->jmax);
#ifdef TIME
        end = clock();
        v_time = (float)((end-start)/((float)CLOCKS_PER_SEC));
#endif

        fprintf(stderr,"done\n");

        /* Debugging purpose. Mike */
        /*
        for(i=0;i<LABELnbr;i++){
            fprintf(stderr,"\t%d\n",area[i]);
        }
        */
        
        

        /* Allocate space of end point of Voronoi Edge */
        SiteMax+=1;
        endp = (EndPoint *)myalloc(sizeof(EndPoint) * SiteMax);
    
        /* Voronoi edge removal */
        fprintf(stderr,"Erasing Voronoi edges...");
#ifdef TIME
        start = clock();
#endif
        erase();

#ifdef TIME
        end = clock();
        e_time = (float)((end-start)/((float)CLOCKS_PER_SEC));
#endif
        fprintf(stderr,"done\n");


        /* neighbor ¤ÎÎÎ°è²òÊü */
        free(neighbor);
        
        /* ¥Ü¥í¥Î¥¤ÊÕ½ÐÎÏ */
#ifdef TIME
        start = clock();
#endif
        
        //unsigned int graph[MY_V][MY_V][2] = {0}; // [:][:][0] <- weight (i.e., 1)
                                  // [:][:][1] <- index of lineseg connecting v1 and v2

        int V = 400; 
        struct Graph* graph = createGraph(V); 

        *nlines = LINEnbr;
        *mlineseg = (LineSegment *)malloc(LINEnbr*sizeof(LineSegment));
        for(int i=0;i<LINEnbr;i++) {
            (*mlineseg)[i] = lineseg[i];
            if(lineseg[i].yn == OUTPUT &&
               (lineseg[i].xs != lineseg[i].xe
                || lineseg[i].ys != lineseg[i].ye)) {
                /*
                printf("[%d] s:(%d,%d) e:(%d,%d) ... sp:%d ep:%d\n",
                        i,
                        lineseg[i].xs,lineseg[i].ys,
                        lineseg[i].xe,lineseg[i].ye,
                        lineseg[i].sp,lineseg[i].ep);
                */
                
                // Build a graph
                addEdge(graph, lineseg[i].sp, lineseg[i].ep, i); 
                
                /*
                graph[lineseg[i].sp][lineseg[i].ep][0]=1;
                graph[lineseg[i].ep][lineseg[i].sp][0]=1;
                graph[lineseg[i].sp][lineseg[i].ep][1]=i;
                graph[lineseg[i].ep][lineseg[i].sp][1]=i;
                */

                edge_nbr++;
            }
        }
        


        printf("\t# of Neighbors (NEIGHnbr): %d\n",NEIGHnbr);
        printf("\t# of Lines (LINEnbr): %d\n",LINEnbr);
        printf("\tArea after removal Voronoi side (edge_nbr): %d\n",edge_nbr);

#ifdef TIME
        end = clock();
        o_time = (float)((end-start)/((float)CLOCKS_PER_SEC));
#endif
        // Output debug information 
        //dnumber(imgd1->imax, imgd1->jmax);

        /*
            FINDING ZONES:
                - DESC.: Find minimum weighted cycle
                - Graph: G(V,E)
                    - V: [(label:0, x:?, y:?), (label:1, x:?, y:?), ... ]
                    - E: [(V1,V2), (V1,V3), ... ]

                - Adjascent matrix: 
                    v1 v2 v3 ... vn
                v1  
                v2
                v3
                ...
                vn
            
            zone <- 0
            FOR e IN E:
                IF e.zone is EMPTY:
                    1- v1,v2 <- v in e:
                    2- temporally delete e from adjacent matrix
                    3- find shortest path from v1 to v2
                    4- e.zone in (the obtained path + e) append zone++
        */
        /*
        for(int i=0; i<V ; i++)
        {
            for(int j=0; j<V ; j++)
            {
                printf("%d ",graph[i][j][1]);
            }
            printf("\n");
        }
        */
        /*
        v1
        v2
        w
        lineseg_idx
        next

        int graph[9][9] = { { 0, 4, 0, 0, 0, 0, 0, 8, 0 }, 
                        { 4, 0, 8, 0, 0, 0, 0, 11, 0 }, 
                        { 0, 8, 0, 7, 0, 4, 0, 0, 2 }, 
                        { 0, 0, 7, 0, 9, 14, 0, 0, 0 }, 
                        { 0, 0, 0, 9, 0, 10, 0, 0, 0 }, 
                        { 0, 0, 4, 14, 10, 0, 2, 0, 0 }, 
                        { 0, 0, 0, 0, 0, 2, 0, 1, 6 }, 
                        { 8, 11, 0, 0, 0, 0, 1, 0, 7 }, 
                        { 0, 0, 2, 0, 0, 0, 6, 7, 0 } }; 
        */

        /* Edge handling - start */
        // 1- find edge like (-1,?) or (?,-1) (i.e., lineseg[i].sp or ep == -1)
        // 2- case by case:
        //    1- edge on top (i.e., lineseg[?].ys or ye == 0):
        //       - points <- topleft, (lineseg[?].xs,lineseg[?].ys OR lineseg[?].xe,lineseg[?].ye), ...
        //       - for point, point+1 in points:
        //          - addEdge(graph,point,point+1,new_lineseg_idx)
        //    2- edge on right (i.e., lineseg[?].xs or xe == WIDTH):
        //    3- edge on bot (i.e., lineseg[?].ys or ye == HEIGHT):
        //    4- edge on left (i.e., lineseg[?].xs or xe == 0):

        // edge_sites contains points on the edge of image.
        struct Site  *edge_sites;
        edge_sites = (struct Site *) myalloc(SITE_BOX*sizeof *sites);
        int edge_sites_idx = 0;

        // Add four corner of image into graph
        int _imin = 0;
        int _imax = imgd1->imax-1;
        int _jmin = 0;
        int _jmax = imgd1->jmax-1;

        int top_left_idx = nsites++;
        edge_sites[edge_sites_idx].coord.x = _imin;
        edge_sites[edge_sites_idx].coord.y = _jmin;
        edge_sites[edge_sites_idx].sitenbr = top_left_idx;
        edge_sites_idx++;

        int top_right_idx = nsites++;
        edge_sites[edge_sites_idx].coord.x = _imax;
        edge_sites[edge_sites_idx].coord.y = _jmin;
        edge_sites[edge_sites_idx].sitenbr = top_right_idx;
        edge_sites_idx++;

        int bot_right_idx = nsites++;
        edge_sites[edge_sites_idx].coord.x = _imax;
        edge_sites[edge_sites_idx].coord.y = _jmax;
        edge_sites[edge_sites_idx].sitenbr = bot_right_idx;
        edge_sites_idx++;
        
        int bot_left_idx = nsites++;
        edge_sites[edge_sites_idx].coord.x = _imin;
        edge_sites[edge_sites_idx].coord.y = _jmax;
        edge_sites[edge_sites_idx].sitenbr = bot_left_idx;
        edge_sites_idx++;
        
        
        /*
            Below for loop collects points (so-called sites) lie on the edge of an image.
        */
        for(int i=0 ; i<LINEnbr ; i++)
        {
            // For valid edges only
            if(lineseg[i].yn == OUTPUT &&
               (lineseg[i].xs != lineseg[i].xe
                || lineseg[i].ys != lineseg[i].ye)) 
            {
                int src = lineseg[i].sp;
                int tar = lineseg[i].ep;
                // 1- find edge like (-1,?) or (?,-1) (i.e., lineseg[i].sp or ep == -1)
                if(src==-1 || tar==-1)
                {      
                    //printf("checkpoint0 ... s:(%.lf,%.lf) e:(%.lf,%.lf) \n",lineseg[i].xs,lineseg[i].ys,lineseg[i].xe,lineseg[i].ye);
                    printf("checkpoint0 _imax:%d _jmax:%d ... s:(%d,%d) e:(%d,%d) \n",
                                        int(_imax),int(_jmax),lineseg[i].xs,lineseg[i].ys,lineseg[i].xe,lineseg[i].ye);
                    // 2- case by case:
                    //    1- edge on top (i.e., lineseg[?].ys or ye == 0):
                    if(lineseg[i].ys == _jmin || lineseg[i].ye == _jmin)
                    {
                        printf("checkpoint1\n");
                        // start-point is on the edge
                        if(lineseg[i].ys == _jmin){
                            edge_sites[edge_sites_idx].coord.x = (float)lineseg[i].xs;
                            edge_sites[edge_sites_idx].coord.y = (float)lineseg[i].ys;
                        }
                        // end-point is on the edge
                        else{
                            edge_sites[edge_sites_idx].coord.x = (float)lineseg[i].xe;
                            edge_sites[edge_sites_idx].coord.y = (float)lineseg[i].xe;
                        }
                        edge_sites[edge_sites_idx].sitenbr = nsites++;
                        edge_sites_idx++;
                    }
                    //    2- edge on right (i.e., lineseg[?].xs or xe == xmax):
                    else if(lineseg[i].xs == _imax || lineseg[i].xe == _imax){
                        printf("checkpoint2\n");
                        // start-point is on the edge
                        if(lineseg[i].xs == _imax){
                            edge_sites[edge_sites_idx].coord.x = (float)lineseg[i].xs;
                            edge_sites[edge_sites_idx].coord.y = (float)lineseg[i].ys;
                        }
                        // end-point is on the edge
                        else{
                            edge_sites[edge_sites_idx].coord.x = (float)lineseg[i].xe;
                            edge_sites[edge_sites_idx].coord.y = (float)lineseg[i].ye;
                        }
                        edge_sites[edge_sites_idx].sitenbr = nsites++;
                        edge_sites_idx++;
                    }
                    //    3- edge on bot (i.e., lineseg[?].ys or ye == ymax):
                    else if(lineseg[i].ys == _jmax || lineseg[i].ye == _jmax){
                        printf("checkpoint3\n");
                        // start-point is on the edge
                        if(lineseg[i].ys == _jmax){
                            edge_sites[edge_sites_idx].coord.x = (float)lineseg[i].xs;
                            edge_sites[edge_sites_idx].coord.y = (float)lineseg[i].ys;
                        }
                        // end-point is on the edge
                        else{
                            edge_sites[edge_sites_idx].coord.x = (float)lineseg[i].xe;
                            edge_sites[edge_sites_idx].coord.y = (float)lineseg[i].ye;
                        }
                        edge_sites[edge_sites_idx].sitenbr = nsites++;
                        edge_sites_idx++;
                    }
                    //    4- edge on left (i.e., lineseg[?].xs or xe == xmin):
                    else if(lineseg[i].xs == _imin || lineseg[i].xe == _imin){
                        printf("checkpoint4\n");
                        // start-point is on the edge
                        if(lineseg[i].xs == _imin){
                            edge_sites[edge_sites_idx].coord.x = (float)lineseg[i].xs;
                            edge_sites[edge_sites_idx].coord.y = (float)lineseg[i].ys;
                        }
                        // end-point is on the edge
                        else{
                            edge_sites[edge_sites_idx].coord.x = (float)lineseg[i].xe;
                            edge_sites[edge_sites_idx].coord.y = (float)lineseg[i].ye;
                        }
                        edge_sites[edge_sites_idx].sitenbr = nsites++;
                        edge_sites_idx++;
                    }
                }
            }
        }    
        
        for(int i=0 ; i<edge_sites_idx ; i++){
            printf("[%d] edge_sites: [%d] (%f,%f)\n",i,edge_sites[i].sitenbr,edge_sites[i].coord.x,edge_sites[i].coord.y);
        }
        
        /*
            Now, connect points in the edge_sites[] to each other.
        */
        
        
        qsort(edge_sites, edge_sites_idx, sizeof(struct Site), compare_struct_y);
        qsort(edge_sites, edge_sites_idx, sizeof(struct Site), compare_struct_x);
        int prev_edge_sites_idx;
        int curr_edge_sites_idx;

        // case 1: edges on the top
        prev_edge_sites_idx = top_left_idx;
        for(int i=0 ; i<edge_sites_idx ; i++)
        {
            if( edge_sites[i].coord.y == _jmin )
            {
                curr_edge_sites_idx = edge_sites[i].sitenbr;
                if(curr_edge_sites_idx == prev_edge_sites_idx)
                    continue;
                addEdge(graph,prev_edge_sites_idx,edge_sites[i].sitenbr,-1);

                lineseg[LINEnbr].sp = prev_edge_sites_idx;
                lineseg[LINEnbr].ep = edge_sites[i].sitenbr;
                lineseg[LINEnbr].yn = OUTPUT;
                lineseg[LINEnbr].zone_idx = 0;
                lineseg[LINEnbr].next = NULL;
                lineseg[LINEnbr].lineseg_idx = LINEnbr;
                LINEnbr++;

                printf("[top] addEdge(%d,%d,graph,lineseg:%d)\n",
                        prev_edge_sites_idx,edge_sites[i].sitenbr,
                        LINEnbr);
                prev_edge_sites_idx = curr_edge_sites_idx;
            }
        }
        // case 3: edges on the bot
        prev_edge_sites_idx = bot_left_idx;
        for(int i=0 ; i<edge_sites_idx ; i++)
        {
            if( edge_sites[i].coord.y == _jmax )
            {
                curr_edge_sites_idx = edge_sites[i].sitenbr;
                if(curr_edge_sites_idx == prev_edge_sites_idx)
                    continue;
                addEdge(graph,prev_edge_sites_idx,edge_sites[i].sitenbr,-1);

                lineseg[LINEnbr].sp = prev_edge_sites_idx;
                lineseg[LINEnbr].ep = edge_sites[i].sitenbr;
                lineseg[LINEnbr].yn = OUTPUT;
                lineseg[LINEnbr].zone_idx = 0;
                lineseg[LINEnbr].next = NULL;
                lineseg[LINEnbr].lineseg_idx = LINEnbr;
                LINEnbr++;

                printf("[bot] addEdge(%d,%d,graph,lineseg:%d)\n",
                        prev_edge_sites_idx,edge_sites[i].sitenbr,
                        LINEnbr);
                prev_edge_sites_idx = curr_edge_sites_idx;
            }
        }

        qsort(edge_sites, edge_sites_idx, sizeof(struct Site), compare_struct_x);
        qsort(edge_sites, edge_sites_idx, sizeof(struct Site), compare_struct_y);
        // case 2: edges on the right
        prev_edge_sites_idx = top_right_idx;
        for(int i=0 ; i<edge_sites_idx ; i++)
        {
            //printf("checkpoint1 edge_sites[%d].coord.x:%f _imax:%d\n",i,edge_sites[i].coord.x,_imax);
            if( edge_sites[i].coord.x == _imax )
            {
                curr_edge_sites_idx = edge_sites[i].sitenbr;
                if(curr_edge_sites_idx == prev_edge_sites_idx)
                    continue;
                addEdge(graph,prev_edge_sites_idx,edge_sites[i].sitenbr,-1);
                lineseg[LINEnbr].sp = prev_edge_sites_idx;
                lineseg[LINEnbr].ep = edge_sites[i].sitenbr;
                lineseg[LINEnbr].yn = OUTPUT;
                lineseg[LINEnbr].zone_idx = 0;
                lineseg[LINEnbr].next = NULL;
                lineseg[LINEnbr].lineseg_idx = LINEnbr;
                LINEnbr++;
                printf("[rignt] addEdge(%d,%d,graph,lineseg:%d)\n",
                        prev_edge_sites_idx,edge_sites[i].sitenbr,
                        LINEnbr);
                prev_edge_sites_idx = curr_edge_sites_idx;
            }
        }
        // case 4: edges on the left
        prev_edge_sites_idx = top_left_idx;
        for(int i=0 ; i<edge_sites_idx ; i++)
        {
            if( edge_sites[i].coord.x == _imin )
            {
                curr_edge_sites_idx = edge_sites[i].sitenbr;
                if(curr_edge_sites_idx == prev_edge_sites_idx)
                    continue;
                addEdge(graph,prev_edge_sites_idx,edge_sites[i].sitenbr,-1);
                lineseg[LINEnbr].sp = prev_edge_sites_idx;
                lineseg[LINEnbr].ep = edge_sites[i].sitenbr;
                lineseg[LINEnbr].yn = OUTPUT;
                lineseg[LINEnbr].zone_idx = 0;
                lineseg[LINEnbr].next = NULL;
                lineseg[LINEnbr].lineseg_idx = LINEnbr;
                LINEnbr++;
                printf("[left] addEdge(%d,%d,graph,lineseg:%d)\n",
                        prev_edge_sites_idx,edge_sites[i].sitenbr,
                        LINEnbr);
                prev_edge_sites_idx = curr_edge_sites_idx;
            }
        }
        /* Edge handling - end */
        
        ZONEnbr = 0;
        lineseg_edge = (LineSegment *)myalloc(sizeof(LineSegment)* INITLINE);
        int lineseg_edge_idx=0;
        for(int i=0 ; i<LINEnbr ; i++)
        {
            /*
            printf("\ncheckpoint:lineseg[%d].yn:%d lineseg[i].xs:%d lineseg[i].xe:%d lineseg[i].ys:%d lineseg[i].ye:%d\n",
                                i,lineseg[i].yn,
                                lineseg[i].xs,lineseg[i].xe,
                                lineseg[i].ys,lineseg[i].ye);
            */
            // For valid edges only
            if(lineseg[i].yn == OUTPUT 
                //&& (lineseg[i].xs != lineseg[i].xe
                //|| lineseg[i].ys != lineseg[i].ye)
                ) {
                //if(lineseg[i].zone_idx<2)
                if(1)
                {
                    // 1- v1,v2 <- v in e:
                    int src = lineseg[i].sp;
                    int tar = lineseg[i].ep;
                    // src or tar is -1 when the lineseg is on the edge of paper. So pass this for now.
                    if(src!=-1 and tar!=-1)
                    {
                        printf("src:%d tar:%d lineseg:%d\n",src,tar,i);
                        // 2- temporally delete e from adjacent matrix
                        delEdge(graph,src,tar);
                        delEdge(graph,tar,src);
                        
                        //graph[src][tar][0] = 0;
                        //graph[tar][src][0] = 0;

                        // 3- find shortest path from v1 to v2
                        
                        dijkstra(graph, src, tar, i);

                        // restore deleted e in adjacent matrix from step 2 
                        addEdge(graph,src,tar,i);
                        addEdge(graph,tar,src,i);
                        //graph[src][tar][0] = 1;
                        //graph[tar][src][0] = 1;
                    }
                }
            }
        }
        
       

        //printGraph(graph); 
        /*
        int _src;
        int _tar;
        struct AdjListNode* pCrawl;
        _src = 126;
        _tar = 122;
        pCrawl = graph->array[_src].head; 
        printf("\n Adjacency list of vertex %d\n head ", _src); 
        while (pCrawl) 
        { 
            printf("-> %d", pCrawl->dest); 
            pCrawl = pCrawl->next; 
        } 
        printf("\n"); 

        // unlink src-dest
        delEdge(graph,126,122);


        _src = 126;
        _tar = 122;
        pCrawl = graph->array[_src].head; 
        printf("\n Adjacency list of vertex %d\n head ", _src); 
        while (pCrawl) 
        { 
            printf("-> %d", pCrawl->dest); 
            pCrawl = pCrawl->next; 
        } 
        printf("\n"); 

        _src = 122;
        _tar = 126;
        pCrawl = graph->array[_src].head;  
        printf("\n Adjacency list of vertex %d\n head ", _src); 
        while (pCrawl) 
        { 
            printf("-> %d", pCrawl->dest); 
            pCrawl = pCrawl->next; 
        } 
        printf("\n"); 

        delEdge(graph,122,126);

        _src = 122;
        _tar = 126;
        pCrawl = graph->array[_src].head;  
        printf("\n Adjacency list of vertex %d\n head ", _src); 
        while (pCrawl) 
        { 
            printf("-> %d", pCrawl->dest); 
            pCrawl = pCrawl->next; 
        } 
        printf("\n"); 

        dijkstra(graph,126,122,70); 
        */



        /*
        int _src = 220;
        int _tar = 209;
        printf("src:%d tar%d (%d,%d)-(%d,%d)\n",
                _src,_tar,
                lineseg[graph[_src][_tar][1]].xs,
                lineseg[graph[_src][_tar][1]].ys,
                lineseg[graph[_src][_tar][1]].xe,
                lineseg[graph[_src][_tar][1]].ye);
        graph[_src][_tar][0] = 0;
        graph[_tar][_src][0] = 0;
        
        dijkstra(graph, _src, _tar); 
        */


        /*
            END FINDING ZONES:
        */

        /* ÎÎ°è²òÊü */
        free(area);
        free(sites);
        free(lineseg);
        free(graph);
        EndPoint point;
        /*
        for(i=0;i<SiteMax;i++){
            while(endp[i].next){
                point=*endp[i].next;
                free(endp[i].next);
                endp[i].next=point.next;
            }
        }
        */
        free(endp);
        freelist_destroy(&hfl);
        freelist_destroy(&efl);
        freelist_destroy(&sfl);
    }

    void set_param(int nm, int sr, float fr, int ta){
        if(nm>=0)
            noise_max = nm;
        if(sr>=0)
            sample_rate = sr;
        if(fr>=0)
            freq_rate = FREQ_RATE;
        if(ta>=0)
            Ta = ta;
    }

    void voronoi_colorseg(ImageData *out_img,
                          ImageData *in_img,
                          bool remove_noise) {
    
        unsigned int nlines=0;
        LineSegment	 *mlineseg;
        voronoi_pageseg(&mlineseg,&nlines,in_img);

        /* setting image size */
        out_img->imax=in_img->imax;
        out_img->jmax=in_img->jmax;
        if((out_img->image=(char *)malloc(in_img->imax*in_img->jmax))==NULL){
            fprintf(stderr,"voronoi_colorseg: not enough memory for image\n");
            exit(1);
        }
        bool noimage = false;
        bit_to_byte(in_img,out_img,noimage);

        if(remove_noise){
            for(int i=0;i<BPnbr; i++){
                int index = bpx[i].xax+(bpx[i].yax*out_img->imax);
                if(noise_comp[bpx[i].label] && index<out_img->imax*out_img->jmax)
                    out_img->image[index] = WHITE;
            }
        }

        for(int i=0;i<nlines;i++){
            if(mlineseg[i].yn == OUTPUT &&
               (mlineseg[i].xs != mlineseg[i].xe
                || mlineseg[i].ys != mlineseg[i].ye)) {
                draw_line(out_img, mlineseg[i].xs, mlineseg[i].ys, 
                          mlineseg[i].xe, mlineseg[i].ye, LINE_C, WIDTH);
                //             fprintf(stderr,"%d %d %d %d\n",
                // 		    mlineseg[i].xs,mlineseg[i].xe,
                // 		    mlineseg[i].ys,mlineseg[i].ye);
            }
        }
        free(bpx);
        free(shape);
        free(noise_comp);
        free(mlineseg);
    }
}

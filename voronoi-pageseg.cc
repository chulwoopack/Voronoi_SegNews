/*
  $Date: 1999/10/15 12:40:27 $
  $Revision: 1.1.1.1 $
  $Author: kise $
  main.c
  
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

    BlackPixel 	*bpx;		/* Coordinates of black pixels and their labels */
    Shape       *shape;
    Zone        *zone;
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

    float max ( float a, float b ) { return a > b ? a : b; }
    float min ( float a, float b ) { return a < b ? a : b; }

    void printProgress (double percentage)
    {
        int val = (int) (percentage * 100);
        int lpad = (int) (percentage * PBWIDTH);
        int rpad = PBWIDTH - lpad;
        printf ("\r\b%3d%% [%.*s%*s]", val, lpad, PBSTR, rpad, "");
        fflush (stdout);
    }

    long getMemoryUsage() 
    {
        struct rusage usage;
        if(0 == getrusage(RUSAGE_SELF, &usage))
            return usage.ru_maxrss; // kilobytes
        else
            return 0;
    }

    /* Function to remove duplicates from a 
   unsorted linked list */
    void removeDuplicates(struct CC *start) 
    { 
        struct CC *ptr1, *ptr2, *dup; 
        ptr1 = start; 
      
        /* Pick elements one by one */
        while (ptr1 != NULL && ptr1->next != NULL) 
        { 
            ptr2 = ptr1; 
      
            /* Compare the picked element with rest 
               of the elements */
            while (ptr2->next != NULL) 
            { 
                /* If duplicate then delete it */
                if (ptr1->lab == ptr2->next->lab) 
                { 
                    /* sequence of steps is important here */
                    dup = ptr2->next; 
                    ptr2->next = ptr2->next->next; 
                    delete(dup); 
                } 
                else /* This is tricky */
                    ptr2 = ptr2->next; 
            } 
            ptr1 = ptr1->next; 
        } 
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

    //
    // for a
    //      for b
    //          comp(a,b)
    bool sameZone(Zone query)
    {
        bool DEBUG = false;
        bool sameLen = false;
        struct AdjListNode* zCrawl;
        struct AdjListNode* qCrawl;
        if(DEBUG){
            printf("**CURR ZONE BOARD**\n");
            for(int i=0 ; i<ZONEnbr ; i++)
            {
                zCrawl = zone[i].head;
                printf("zone[%d] \n head \n",i);
                while(zCrawl)
                {
                    printf("-> %d ",zCrawl->lineseg_idx);
                    zCrawl = zCrawl->next;
                }
                printf("\n");
            }
        }
        
        for(int i=0 ; i<ZONEnbr-1 ; i++)
        {
            zCrawl = zone[i].head;
            qCrawl = query.head;

            if(DEBUG) printf("\t[sameZone] comparing zone[%d].len:%d ... query.len:%d\n",i,zone[i].len,query.len);
            if(zone[i].len != query.len)
                continue;
            else{
                // Loop query sequence
                while(qCrawl)
                {
                    if(DEBUG) printf("\t\t[sameZone] qCrawl:%d to ",qCrawl->lineseg_idx);
                    zCrawl = zone[i].head;
                    bool newSeq = true;
                    // Loop previously found zone's lineseg sequence
                    // if newly found zone's sequence contains at least one new lineseg, return False.
                    while(zCrawl)
                    {
                        if(DEBUG) printf("%d ",zCrawl->lineseg_idx);
                        if(qCrawl->lineseg_idx==zCrawl->lineseg_idx)
                        {
                            if(DEBUG) printf("... exist! \n",zCrawl->lineseg_idx,i);
                            newSeq = false;
                            break;
                        }
                        zCrawl = zCrawl->next;
                    }
                    // Sequence is found, early termination.
                    if(qCrawl->next==NULL and newSeq==false){
                        return true;
                    }
                    qCrawl = qCrawl->next;
                }
            }
        } 
        if(DEBUG) printf("\t\t[sameZone] no same sequence is found ... return false\n");
        return false;
    }



    void assignZone(struct Graph* graph, int dist[], int path[], int n, int src, int tar, int lineseg_idx_src_tar)
    {
        bool DEBUG = false;
        if(DEBUG) printf("[assignZone] src:%d tar:%d\n",src,tar);
        int parent = tar;
        int lineseg_idx;
        struct AdjListNode* pCrawl;
        struct AdjListNode* newNode;
        struct CC* newCC;

        // Get path[tar-...]
        while(path[parent]!=src)
        {
            pCrawl = graph->array[parent].head; 
            while(pCrawl)
            {
                if(pCrawl->dest==path[parent])
                {
                    // path is found!
                    lineseg_idx = pCrawl->lineseg_idx;
                    break;
                }
                pCrawl = pCrawl->next;
            }
            if(DEBUG) printf("[tar-...] lineseg[%d](lab:%d-lab:%d): %d -> %d \n",lineseg_idx,lineseg[lineseg_idx].lab1,lineseg[lineseg_idx].lab2,parent,path[parent]);
            
            newNode = newAdjListNode(-2,lineseg_idx,-2); 
            newNode->next = zone[ZONEnbr].head; 
            zone[ZONEnbr].head = newNode;
            zone[ZONEnbr].len++;

            newCC = (struct CC*) myalloc(sizeof(struct CC));
            newCC->lab = lineseg[lineseg_idx].lab1;
            newCC->next = zone[ZONEnbr].cc_head;
            zone[ZONEnbr].cc_head = newCC;
            newCC = (struct CC*) myalloc(sizeof(struct CC));
            newCC->lab = lineseg[lineseg_idx].lab2;
            newCC->next = zone[ZONEnbr].cc_head;
            zone[ZONEnbr].cc_head = newCC;

            parent = path[parent];
        }

        // Get path[...-src]
        pCrawl = graph->array[parent].head; 
        while(pCrawl)
        {
            if(pCrawl->dest==path[parent])
            {
                lineseg_idx = pCrawl->lineseg_idx;
                // path is found!
                break;
            }
            pCrawl = pCrawl->next;
        }
        if(DEBUG) printf("[...-src] lineseg[%d](lab:%d-lab:%d): %d -> %d \n",lineseg_idx,lineseg[lineseg_idx].lab1,lineseg[lineseg_idx].lab2,parent,path[parent]);
    
        newNode = newAdjListNode(-2,lineseg_idx,-2); 
        newNode->next = zone[ZONEnbr].head; 
        zone[ZONEnbr].head = newNode;
        zone[ZONEnbr].len++;

        newCC = (struct CC*) myalloc(sizeof(struct CC));
        newCC->lab = lineseg[lineseg_idx].lab1;
        newCC->next = zone[ZONEnbr].cc_head;
        zone[ZONEnbr].cc_head = newCC;
        newCC = (struct CC*) myalloc(sizeof(struct CC));
        newCC->lab = lineseg[lineseg_idx].lab2;
        newCC->next = zone[ZONEnbr].cc_head;
        zone[ZONEnbr].cc_head = newCC;
        
        // Get path[src-tar]
        if(DEBUG) printf("[src-tar] lineseg[%d](lab:%d-lab:%d): %d -> %d \n",lineseg_idx_src_tar,lineseg[lineseg_idx_src_tar].lab1,lineseg[lineseg_idx_src_tar].lab2,src,tar);
        newNode = newAdjListNode(-2,lineseg_idx_src_tar,-2); 
        newNode->next = zone[ZONEnbr].head; 
        zone[ZONEnbr].head = newNode;
        zone[ZONEnbr].len++;

        newCC = (struct CC*) myalloc(sizeof(struct CC));
        newCC->lab = lineseg[lineseg_idx_src_tar].lab1;
        newCC->next = zone[ZONEnbr].cc_head;
        zone[ZONEnbr].cc_head = newCC;
        newCC = (struct CC*) myalloc(sizeof(struct CC));
        newCC->lab = lineseg[lineseg_idx_src_tar].lab2;
        newCC->next = zone[ZONEnbr].cc_head;
        zone[ZONEnbr].cc_head = newCC;
        
        ZONEnbr++;

        if(DEBUG) printf("Found %d ZONE(s) \n\n",ZONEnbr-1);
        if(DEBUG) printf("NEXT ZONE NBR:%d \n",ZONEnbr);
        
        if(ZONEnbr>1 and sameZone(zone[ZONEnbr-1]))
        {
            if(DEBUG) printf("\t[WARNING] This zone seems to be visited ... so deleting lastly added zone...\n");
            zone[ZONEnbr-1].head = NULL;
            zone[ZONEnbr-1].len = 0;
            ZONEnbr--;
        }
    }

    // Given three colinear points p, q, r, the function checks if 
    // point q lies on line segment 'pr' 
    bool onSegment(Point p, Point q, Point r) 
    { 
        if (q.x <= max(p.x, r.x) && q.x >= min(p.x, r.x) && 
                q.y <= max(p.y, r.y) && q.y >= min(p.y, r.y)) 
            return true; 
        return false; 
    } 

    // To find orientation of ordered triplet (p, q, r). 
    // The function returns following values 
    // 0 --> p, q and r are colinear 
    // 1 --> Clockwise 
    // 2 --> Counterclockwise 
    int orientation(Point p, Point q, Point r) 
    { 
        int val = (q.y - p.y) * (r.x - q.x) - 
                  (q.x - p.x) * (r.y - q.y); 
      
        if (val == 0) return 0;  // colinear 
        return (val > 0)? 1: 2; // clock or counterclock wise 
    } 
    // The function that returns true if line segment 'p1q1' 
    // and 'p2q2' intersect. 
    bool doIntersect(Point p1, Point q1, Point p2, Point q2) 
    { 
        bool DEBUG = false;
        // Find the four orientations needed for general and 
        // special cases 
        int o1 = orientation(p1, q1, p2); 
        int o2 = orientation(p1, q1, q2); 
        int o3 = orientation(p2, q2, p1); 
        int o4 = orientation(p2, q2, q1); 
      
        // General case 
        if (o1 != o2 && o3 != o4) {
            if(DEBUG) printf("[doIntersect] general case ... p1q1:(%f,%f)-(%f,%f) p2q2:(%f,%f)-(%f,%f)\n",p1.x,p1.y,q1.x,q1.y,p2.x,p2.y,q2.x,q2.y);
            return true; 
        }
            
      
        // Special Cases 
        // p1, q1 and p2 are colinear and p2 lies on segment p1q1 
        if (o1 == 0 && onSegment(p1, p2, q1)){
            if(DEBUG) printf("[doIntersect] colinear ... (%f,%f) lies on segment (%f,%f)-(%f,%f)\n",p2.x,p2.y,p1.x,p1.y,q1.x,q1.y);
            return true; 
        } 
      
        // p1, q1 and p2 are colinear and q2 lies on segment p1q1 
        if (o2 == 0 && onSegment(p1, q2, q1)){
            if(DEBUG) printf("[doIntersect] colinear ... (%f,%f) lies on segment (%f,%f)-(%f,%f)\n",q2.x,q2.y,p1.x,p1.y,q1.x,q1.y);
            return true;   
        } 
      
        // p2, q2 and p1 are colinear and p1 lies on segment p2q2 
        if (o3 == 0 && onSegment(p2, p1, q2)){
            if(DEBUG) printf("[doIntersect] colinear ... (%f,%f) lies on segment (%f,%f)-(%f,%f)\n",p1.x,p1.y,p2.x,p2.y,q2.x,q2.y);
            return true;   
        } 
      
         // p2, q2 and q1 are colinear and q1 lies on segment p2q2 
        if (o4 == 0 && onSegment(p2, q1, q2)){
            if(DEBUG) printf("[doIntersect] colinear ... (%f,%f) lies on segment (%f,%f)-(%f,%f)\n",q1.x,q1.y,p2.x,p2.y,q2.x,q2.y);
            return true;   
        } 
      
        if(DEBUG) printf("[doIntersect] none ... p1q1:(%f,%f)-(%f,%f) p2q2:(%f,%f)-(%f,%f)\n",p1.x,p1.y,q1.x,q1.y,p2.x,p2.y,q2.x,q2.y);
        return false; // Doesn't fall in any of the above cases 
    } 
    // Returns true if the point p lies inside the polygon[] with n vertices 
    bool isInside(Point* polygon, int n, Point p) 
    { 
        bool DEBUG = false;
        // There must be at least 3 vertices in polygon[] 
        if (n < 3)  return false; 
      
        // Create a point for line segment from p to infinite 
        Point extreme = {IMG_IMAX, p.y}; 
      
        // Count intersections of the above line with sides of polygon 
        int count = 0, i = 0; 
        do
        { 
            int next = (i+1)%n; 
            // Check if the line segment from 'p' to 'extreme' intersects 
            // with the line segment from 'polygon[i]' to 'polygon[next]' 
            if (doIntersect(*(polygon+i), *(polygon+next), p, extreme)) 
            { 
                // If the point 'p' is colinear with line segment 'i-next', 
                // then check if it lies on segment. If it lies, return true, 
                // otherwise false 
                if (orientation(*(polygon+i), p, *(polygon+next)) == 0) 
                   return onSegment(*(polygon+i), p, *(polygon+next)); 
                if(DEBUG) printf("[isInside] intersect!\n");
                count++; 
            } 
            i = next; 
        } while (i != 0); 
      
        // Return true if count is odd, false otherwise 
        return count&1;  // Same as (count%2 == 1) 
    } 

    void CountCCsInZone(int zone_idx, Point p)
    {
        bool DEBUG = false;
        /*
        int i = 0;
        int n = 4;//zone[zone_idx].len;
        
        Point p = {5, 5};
        Point* polygon = (Point*) malloc(n * sizeof(Point));
        
        (polygon+i)->x = 0;
        (polygon+i)->y = 0;
        i++;

        (polygon+i)->x = 0;
        (polygon+i)->y = 10;
        i++;

        (polygon+i)->x = 10;
        (polygon+i)->y = 10;
        i++;


        (polygon+i)->x = 10;
        (polygon+i)->y = 0;
        i++;
        */


        

        /*
        int i = 0;
        int n = 3;
        
        Point p = {4, 4};
        Point* polygon = (Point*) malloc(n * sizeof(Point));
        
        (polygon+i)->x = 0;
        (polygon+i)->y = 0;
        i++;

        (polygon+i)->x = 5;
        (polygon+i)->y = 5;
        i++;

        (polygon+i)->x = 5;
        (polygon+i)->y = 0;
        */
        

        
        int i =0;
        int n = zone[zone_idx].len;
        int s_or_e = -1; // 0:start 1:end
        //Point p = {215, 168};
        Point* polygon = (Point*) malloc(n * sizeof(Point));
        struct AdjListNode* pCrawl = zone[zone_idx].head;

        if(DEBUG) printf("\n[CountCCsInZone] point ... (%f,%f)\n",p.x,p.y);
        while(pCrawl)
        {
            if(DEBUG) printf("[CountCCsInZone] lineseg[%d] (%d,%d), (%d,%d)\n",pCrawl->lineseg_idx,lineseg[pCrawl->lineseg_idx].xs,lineseg[pCrawl->lineseg_idx].ys,lineseg[pCrawl->lineseg_idx].xe,lineseg[pCrawl->lineseg_idx].ye);
            // To prevent segment fault
            if(pCrawl->next != NULL)
            {
                // case 1: curr_lineseg.start == next_lineseg.start or next_lineseg.end
                if((lineseg[pCrawl->lineseg_idx].xs==lineseg[pCrawl->next->lineseg_idx].xs 
                    and lineseg[pCrawl->lineseg_idx].ys==lineseg[pCrawl->next->lineseg_idx].ys)
                    or
                   (lineseg[pCrawl->lineseg_idx].xs==lineseg[pCrawl->next->lineseg_idx].xe 
                    and lineseg[pCrawl->lineseg_idx].ys==lineseg[pCrawl->next->lineseg_idx].ye))
                {
                    s_or_e = 0;
                }
                // case 2: curr_lineseg.end == next_lineseg.start or next_lineseg.end
                else
                {
                    s_or_e = 1;
                }
            }
            // case 3: special case: last lineseg.
            if(i==n-1)
            {
                
                (polygon+i)->x = lineseg[pCrawl->lineseg_idx].xs;
                (polygon+i)->y = lineseg[pCrawl->lineseg_idx].ys;
                i++;
                (polygon+i)->x = lineseg[pCrawl->lineseg_idx].xe;
                (polygon+i)->y = lineseg[pCrawl->lineseg_idx].ye;
                i++;
                
                /*
                (polygon+i)->x = 123;
                (polygon+i)->y = 123;
                i++;
                (polygon+i)->x = 123;
                (polygon+i)->y = 123;
                i++;
                */

            }
            else
            {
                if(s_or_e==0)
                {
                    (polygon+i)->x = lineseg[pCrawl->lineseg_idx].xs;
                    (polygon+i)->y = lineseg[pCrawl->lineseg_idx].ys;
                    i++;
                }
                else if (s_or_e==1)
                {
                    (polygon+i)->x = lineseg[pCrawl->lineseg_idx].xe;
                    (polygon+i)->y = lineseg[pCrawl->lineseg_idx].ye;
                    i++;
                }
            }
            pCrawl = pCrawl->next;
        }

        if(DEBUG)
        {
            printf("[CountCCsInZone] polygon ... \n");
            for(int i=0 ; i<n ; i++)
            {
                printf("[CountCCsInZone] (%f,%f)\n",(polygon+i)->x,(polygon+i)->y);
            }
        }

        if(isInside(polygon, n, p))
        {
            if(DEBUG) printf("Yes \n");
            zone[zone_idx].numOfCCs++;
        }
        else
        {
            if(DEBUG) printf("No \n"); 
        }
        
    }

    // The function that checking if there are more than 3 Voronoi-edges (lineseg) attached to a single Voronoi-point (site).
    bool isForked(struct Graph* graph, int src, int tar)
    {
        int numEdges = 0;
        struct AdjListNode* pCrawl = graph->array[src].head;
        while(pCrawl)
        {
            numEdges++;
            pCrawl = pCrawl->next;
        }
        if(numEdges<3)
            return false;
        else
            return true;
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
            assignZone(graph,dist,path,V,src,tar,lineseg_idx);
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

    // A utility function to print the adjacency list  
    // representation of graph 
    void printGraph(struct Graph* graph) 
    { 
        int v; 
        for (v = 0; v < graph->V; ++v) 
        { 
            struct AdjListNode* pCrawl = graph->array[v].head; 
            printf("\n Adjacency list of vertex %d \n head ", v); 
            while (pCrawl) 
            { 
                printf("-> %d (lineseg:%d)", pCrawl->dest,pCrawl->lineseg_idx); 
                pCrawl = pCrawl->next; 
            } 
            printf("\n"); 
        } 
    } 

    // Adds an edge to an undirected graph 
    void addEdge(struct Graph* graph, int src, int dest, int lineseg_idx, int weight) 
    { 
        // Add an edge from src to dest.  A new node is  
        // added to the adjacency list of src.  The node 
        // is added at the begining 
        struct AdjListNode* newNode = newAdjListNode(dest,lineseg_idx,weight); 
        newNode->next = graph->array[src].head; 
        graph->array[src].head = newNode; 
      
        // Since graph is undirected, add an edge from 
        // dest to src also 
        newNode = newAdjListNode(src,lineseg_idx,weight); 
        newNode->next = graph->array[dest].head; 
        graph->array[dest].head = newNode; 
    } 

    void delEdge(struct Graph* graph, int src, int dest)
    {
        bool DEBUG = false;
        struct AdjListNode* pCrawl;
        struct AdjListNode* temp;
        struct AdjListNode* pDebug;
        // unlink src-dest
        pCrawl = graph->array[src].head;
        if(DEBUG){
            printf("[delEdge] src:%d dest:%d\n",src,dest);
            //printf("[delEdge] \tpCrawl->next->dest:%d pCrawl->dest:%d\n",pCrawl->next->dest,pCrawl->dest);
            pDebug = graph->array[src].head;
            printf("[delEdge] BEFORE DELETION ... graph[%d].head ",src);
            while(pDebug)
            {
                printf("-> %d ",pDebug->dest);
                pDebug = pDebug->next;
            }
            printf("\n");
        } 
        while (pCrawl) 
        { 
            if (DEBUG) printf("[delEdge] \tpCrawl: %d\n",pCrawl->dest);
            if(graph->array[src].head->dest==dest){
                // hmm... should I free something here?
                
                temp = graph->array[src].head;
                graph->array[src].head = graph->array[src].head->next;
                //free(temp);
                
                //graph->array[src].head = graph->array[src].head->next;
                if (DEBUG) printf("[delEdge] \tdeleted.\n");
                break;
            }
            else if (pCrawl->next->dest==dest){
                pCrawl->next = pCrawl->next->next;
                temp = pCrawl->next;
                //free(temp);
                if (DEBUG) printf("[delEdge] \tdeleted.\n");
                break;
            }
            else{
                if (DEBUG) printf("[delEdge] \tgetNext()\n");
                pCrawl = pCrawl->next; 
                //free(temp);
            }
        } 

        if(DEBUG){
            pDebug = graph->array[src].head;
            printf("[delEdge] AFTER DELETION ... graph[%d].head ",src);
            while(pDebug)
            {
                printf("-> %d ",pDebug->dest);
                pDebug = pDebug->next;
            }
            printf("\n");
        }    
    }
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
        bool DEBUG = false;

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

        zone =(Zone *)myalloc(sizeof(Zone)* ZONEMAX);
        for (int i = 0; i < ZONEMAX; ++i) {
            zone[i].head = NULL; 
            zone[i].cc_head = NULL;
            zone[i].len = 0;
            zone[i].numOfCCs = 0;
        }
            

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

        /* area[ln] */
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
        //erase();

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
        
      
        int V = 2*nsites; 
        struct Graph* graph = createGraph(V); 

        *nlines = LINEnbr;
        *mlineseg = (LineSegment *)malloc(LINEnbr*sizeof(LineSegment));
        for(int i=0;i<LINEnbr;i++) {
            (*mlineseg)[i] = lineseg[i];
            if(lineseg[i].yn == OUTPUT){
                edge_nbr++;
                // Build a graph
                addEdge(graph, lineseg[i].sp, lineseg[i].ep, i, lineseg[i].weight); 
            }
            else if(lineseg[i].xs == lineseg[i].xe
                    and lineseg[i].ys == lineseg[i].ye)
            {
                if(lineseg[i].sp!=-1){
                    // Build a graph
                    addEdge(graph, lineseg[i].sp, lineseg[i].ep, i, lineseg[i].weight); 
                }
                    
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

        nsites++;
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
                        // start-point is on the edge
                        if(lineseg[i].ys == _jmin){
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
        // prev_edge_sites_idx and curr_edge_sites_idx are used for sites[]
        int prev_edge_sites_idx;
        int curr_edge_sites_idx;
        // prev_edge_sites_idx_temp and curr_edge_sites_idx_temp are used for edge_sites[]
        int prev_edge_sites_idx_temp;
        // line_len is for assigning weight to lineseg
        int line_len;
        int edge_weight = 100;
        
        // case 1: edges on the top
        prev_edge_sites_idx = top_left_idx;
        for(int i=0 ; i<edge_sites_idx ; i++)
        {
            if( edge_sites[i].coord.y == _jmin )
            {
                curr_edge_sites_idx = edge_sites[i].sitenbr;
                if(curr_edge_sites_idx == prev_edge_sites_idx){
                    prev_edge_sites_idx_temp = i;
                    continue;
                }
                line_len = int(edge_sites[i].coord.x-edge_sites[prev_edge_sites_idx_temp].coord.x)*edge_weight;
                addEdge(graph,prev_edge_sites_idx,edge_sites[i].sitenbr,LINEnbr,line_len);

                lineseg[LINEnbr].xs = edge_sites[prev_edge_sites_idx_temp].coord.x;
                lineseg[LINEnbr].ys = edge_sites[prev_edge_sites_idx_temp].coord.y;
                lineseg[LINEnbr].xe = edge_sites[i].coord.x;
                lineseg[LINEnbr].ye = edge_sites[i].coord.y;

                lineseg[LINEnbr].sp = prev_edge_sites_idx;
                lineseg[LINEnbr].ep = edge_sites[i].sitenbr;
                lineseg[LINEnbr].yn = OUTPUT;
                lineseg[LINEnbr].weight = line_len;
                lineseg[LINEnbr].next = NULL;
                lineseg[LINEnbr].lineseg_idx = LINEnbr;

                printf("[top] addEdge(%d,%d,graph,lineseg:%d,weight:%d)\n",
                        prev_edge_sites_idx,edge_sites[i].sitenbr,
                        LINEnbr,
                        line_len);

                LINEnbr++;
                prev_edge_sites_idx = curr_edge_sites_idx;
                prev_edge_sites_idx_temp = i;
            }
        }
        // case 3: edges on the bot
        prev_edge_sites_idx = bot_left_idx;
        for(int i=0 ; i<edge_sites_idx ; i++)
        {
            if( edge_sites[i].coord.y == _jmax )
            {
                curr_edge_sites_idx = edge_sites[i].sitenbr;
                if(curr_edge_sites_idx == prev_edge_sites_idx){
                    prev_edge_sites_idx_temp = i;
                    continue;
                }
                line_len = int(edge_sites[i].coord.x-edge_sites[prev_edge_sites_idx_temp].coord.x)*edge_weight;
                addEdge(graph,prev_edge_sites_idx,edge_sites[i].sitenbr,LINEnbr,line_len);

                lineseg[LINEnbr].xs = edge_sites[prev_edge_sites_idx_temp].coord.x;
                lineseg[LINEnbr].ys = edge_sites[prev_edge_sites_idx_temp].coord.y;
                lineseg[LINEnbr].xe = edge_sites[i].coord.x;
                lineseg[LINEnbr].ye = edge_sites[i].coord.y;

                lineseg[LINEnbr].sp = prev_edge_sites_idx;
                lineseg[LINEnbr].ep = edge_sites[i].sitenbr;
                lineseg[LINEnbr].yn = OUTPUT;
                lineseg[LINEnbr].weight = line_len;
                lineseg[LINEnbr].next = NULL;
                lineseg[LINEnbr].lineseg_idx = LINEnbr;

                printf("[bot] addEdge(%d,%d,graph,lineseg:%d,weight:%d)\n",
                        prev_edge_sites_idx,edge_sites[i].sitenbr,
                        LINEnbr,
                        line_len);
                LINEnbr++;
                prev_edge_sites_idx = curr_edge_sites_idx;
                prev_edge_sites_idx_temp = i;
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
                if(curr_edge_sites_idx == prev_edge_sites_idx){
                    prev_edge_sites_idx_temp = i;
                    continue;
                }
                line_len = int(edge_sites[i].coord.y-edge_sites[prev_edge_sites_idx_temp].coord.y)*edge_weight;
                addEdge(graph,prev_edge_sites_idx,edge_sites[i].sitenbr,LINEnbr,line_len);

                lineseg[LINEnbr].xs = edge_sites[prev_edge_sites_idx_temp].coord.x;
                lineseg[LINEnbr].ys = edge_sites[prev_edge_sites_idx_temp].coord.y;
                lineseg[LINEnbr].xe = edge_sites[i].coord.x;
                lineseg[LINEnbr].ye = edge_sites[i].coord.y;

                lineseg[LINEnbr].sp = prev_edge_sites_idx;
                lineseg[LINEnbr].ep = edge_sites[i].sitenbr;
                lineseg[LINEnbr].yn = OUTPUT;
                lineseg[LINEnbr].weight = line_len;
                lineseg[LINEnbr].next = NULL;
                lineseg[LINEnbr].lineseg_idx = LINEnbr;
                printf("[right] addEdge(%d,%d,graph,lineseg:%d,weight:%d)\n",
                        prev_edge_sites_idx,edge_sites[i].sitenbr,
                        LINEnbr,
                        line_len);
                LINEnbr++;
                prev_edge_sites_idx = curr_edge_sites_idx;
                prev_edge_sites_idx_temp = i;
            }
        }
        // case 4: edges on the left
        prev_edge_sites_idx = top_left_idx;
        for(int i=0 ; i<edge_sites_idx ; i++)
        {
            if( edge_sites[i].coord.x == _imin )
            {
                curr_edge_sites_idx = edge_sites[i].sitenbr;
                if(curr_edge_sites_idx == prev_edge_sites_idx){
                    prev_edge_sites_idx_temp = i;
                    continue;
                }
                line_len = int(edge_sites[i].coord.y-edge_sites[prev_edge_sites_idx_temp].coord.y)*edge_weight;
                addEdge(graph,prev_edge_sites_idx,edge_sites[i].sitenbr,LINEnbr,line_len);
                
                lineseg[LINEnbr].xs = edge_sites[prev_edge_sites_idx_temp].coord.x;
                lineseg[LINEnbr].ys = edge_sites[prev_edge_sites_idx_temp].coord.y;
                lineseg[LINEnbr].xe = edge_sites[i].coord.x;
                lineseg[LINEnbr].ye = edge_sites[i].coord.y;
                
                lineseg[LINEnbr].sp = prev_edge_sites_idx;
                lineseg[LINEnbr].ep = edge_sites[i].sitenbr;
                lineseg[LINEnbr].yn = OUTPUT;
                lineseg[LINEnbr].weight = line_len;
                lineseg[LINEnbr].next = NULL;
                lineseg[LINEnbr].lineseg_idx = LINEnbr;
                printf("[left] addEdge(%d,%d,graph,lineseg:%d,weight:%d)\n",
                        prev_edge_sites_idx,edge_sites[i].sitenbr,
                        LINEnbr,
                        line_len);
                LINEnbr++;
                prev_edge_sites_idx = curr_edge_sites_idx;
                prev_edge_sites_idx_temp = i;
            }
        }

        /*
            TO CONNECT NEWLY ADDED SITES ON THE EDGE OF AN IMAGE TO LINESEGMENT SUCH AS ( EDGE---CC or CC---EDGE)
        */
        for(int i=0 ; i<LINEnbr ; i++)
        {
            // For valid edges only
            if(lineseg[i].yn == OUTPUT )
            {
                int src = lineseg[i].sp;
                int tar = lineseg[i].ep;
                if((src==-1 && tar!=-1) or (src!=-1 && tar==-1))
                {
                    if(DEBUG){
                        printf("src:%d tar:%d lineseg:%d (sp:(%d,%d) ep:(%d,%d))\n",src,tar,i,
                                                                                lineseg[i].xs,lineseg[i].ys,
                                                                                lineseg[i].xe,lineseg[i].ye);
                    }
                    // Find corresponding edge_site
                    if(src==-1){
                        for(int e=0 ; e<edge_sites_idx ; e++)
                        {
                            if(lineseg[i].xs==edge_sites[e].coord.x && lineseg[i].ys==edge_sites[e].coord.y)
                            {
                                lineseg[i].sp = edge_sites[e].sitenbr;
                                delEdge(graph,tar,-1);
                                addEdge(graph,lineseg[i].sp,lineseg[i].ep,i,1);
                                break;
                            }
                        }
                    }
                    else{
                        for(int e=0 ; e<edge_sites_idx ; e++)
                        {
                            if(lineseg[i].xe==edge_sites[e].coord.x && lineseg[i].ye==edge_sites[e].coord.y)
                            {
                                lineseg[i].ep = edge_sites[e].sitenbr;
                                delEdge(graph,src,-1);
                                addEdge(graph,src,lineseg[i].ep,i,1);
                                break;
                            }
                        }
                    }

                    
                }
            }
        }

        /* Edge handling - end */
        //printGraph(graph);
        //printGraph(graph);

        ZONEnbr = 0;
        //lineseg_edge = (LineSegment *)myalloc(sizeof(LineSegment)* INITLINE);
        //int lineseg_edge_idx=0;
        printf("\nFINDING ZONES...\n\n");
        for(int i=0 ; i<LINEnbr ; i++)
        {
            
            //printf("\ncheckpoint:lineseg[%d].yn:%d lineseg[i].xs:%d lineseg[i].xe:%d lineseg[i].ys:%d lineseg[i].ye:%d\n",
            //                    i,lineseg[i].yn,
            //                lineseg[i].xs,lineseg[i].xe,
            //                    lineseg[i].ys,lineseg[i].ye);
            
            // For valid edges only
            if(lineseg[i].yn == OUTPUT 
                || (lineseg[i].xs == lineseg[i].xe and lineseg[i].ys == lineseg[i].ye)
                ) {
                // 1- v1,v2 <- v in e:
                int src = lineseg[i].sp;
                int tar = lineseg[i].ep;
                // src or tar is -1 when the lineseg is on the edge of paper. So pass this for now.
                if(src!=-1 && tar!=-1)
                {
                    //printf("\nFINDING ZONES...\n");
                    printProgress(double(i)/double(LINEnbr));
                    if(DEBUG) printf("lineseg[%d] sp[%d]:(%d,%d) ep[%d]:(%d,%d) weight:%d OUTPUT:%d\n",i,lineseg[i].sp,lineseg[i].xs,lineseg[i].ys,lineseg[i].ep,lineseg[i].xe,lineseg[i].ye,lineseg[i].weight,(lineseg[i].yn == OUTPUT));
                    if(isForked(graph,src,tar)==true or isForked(graph,tar,src)==true)
                    {
                        // 2- temporally delete e from adjacent matrix
                        delEdge(graph,src,tar);
                        //printf("checkpoint2\n");
                        delEdge(graph,tar,src);
                        //printf("checkpoint3\n");
                        
                        // 3- find shortest path from v1 to v2
                        //printGraph(graph);
                        dijkstra(graph, src, tar, i);

                        // restore deleted e in adjacent matrix from step 2 
                        addEdge(graph,src,tar,i,lineseg[i].weight);

                        
                    }
                }
            }
        }
        
        
        
        struct AdjListNode* zCrawl;
        struct CC* cCrawl;
        struct Point targetCC;
        int numOfNoiseZone = 0;
        printf("\n\n**FINAL ZONE BOARD (%d ZONE(s) TOTAL)**\n",ZONEnbr);
        for(int i=0 ; i<ZONEnbr ; i++)
        {
            zCrawl = zone[i].head;
            printf("zone[%d] \n head \n",i);
            while(zCrawl)
            {
                printf("-> %d ",zCrawl->lineseg_idx);
                zCrawl = zCrawl->next;
            }
            cCrawl = zone[i].cc_head;
            removeDuplicates(cCrawl);
            //printf("\n cc_head \n",i);
            while(cCrawl)
            {
                //printf("-> %d (%d,%d) ",cCrawl->lab,shape[cCrawl->lab].x_min,shape[cCrawl->lab].y_min);
                targetCC.x = shape[cCrawl->lab].x_min+0.5;
                targetCC.y = shape[cCrawl->lab].y_min+0.5;
                CountCCsInZone(i,targetCC);

                cCrawl = cCrawl->next;
            }
            if(zone[i].numOfCCs<2) numOfNoiseZone++;
            printf("\nTotal %d CCs\n",zone[i].numOfCCs);
            printf("\n\n");
        }

        printf("\nTotal %d noisy zone(s)\n",numOfNoiseZone);

        
/*
        
        // Before unlink
        int _src;
        int _tar;
        int _lineseg_idx;

        struct AdjListNode* pCrawl;
        _lineseg_idx = 467;
        _src = lineseg[_lineseg_idx].sp;
        _tar = lineseg[_lineseg_idx].ep;

        printf("\nlineseg[%d] sp[%d]:(%d,%d) ep[%d]:(%d,%d) weight:%d\n\tOUTPUT:%d 2nd_Cond: %d\n",
                _lineseg_idx,lineseg[_lineseg_idx].sp,lineseg[_lineseg_idx].xs,lineseg[_lineseg_idx].ys,lineseg[_lineseg_idx].ep,lineseg[_lineseg_idx].xe,lineseg[_lineseg_idx].ye,lineseg[_lineseg_idx].weight,
                lineseg[_lineseg_idx].yn,(lineseg[_lineseg_idx].xs != lineseg[_lineseg_idx].xe || lineseg[_lineseg_idx].ys != lineseg[_lineseg_idx].ye));

        pCrawl = graph->array[_src].head; 
        printf("\n [Before Del] Adjacency list of vertex %d\n head ", _src); 
        while (pCrawl) 
        { 
            printf("-> %d", pCrawl->dest); 
            pCrawl = pCrawl->next; 
        } 
        printf("\n"); 
        pCrawl = graph->array[_tar].head; 
        printf("\n [Before Del] Adjacency list of vertex %d\n head ", _tar); 
        while (pCrawl) 
        { 
            printf("-> %d", pCrawl->dest); 
            pCrawl = pCrawl->next; 
        } 
        printf("\n"); 



        // unlink src-dest
        delEdge(graph,_src,_tar);
        delEdge(graph,_tar,_src);



        // After unlink
        pCrawl = graph->array[_src].head; 
        printf("\n [After Del] Adjacency list of vertex %d\n head ", _src); 
        while (pCrawl) 
        { 
            printf("-> %d", pCrawl->dest); 
            pCrawl = pCrawl->next; 
        } 
        printf("\n"); 
        pCrawl = graph->array[_tar].head; 
        printf("\n [After Del] Adjacency list of vertex %d\n head ", _tar); 
        while (pCrawl) 
        { 
            printf("-> %d", pCrawl->dest); 
            pCrawl = pCrawl->next; 
        } 
        printf("\n"); 
        //printGraph(graph);
        dijkstra(graph,_src,_tar,_lineseg_idx); 

        // link src-tar
        addEdge(graph,_src,_tar,_lineseg_idx,lineseg[_lineseg_idx].weight);


        // After link
        pCrawl = graph->array[_src].head;  
        printf("\n [After Add] Adjacency list of vertex %d\n head ", _src); 
        while (pCrawl) 
        { 
            printf("-> %d", pCrawl->dest); 
            pCrawl = pCrawl->next; 
        } 
        printf("\n"); 
        // After link
        pCrawl = graph->array[_tar].head;  
        printf("\n [After Add] Adjacency list of vertex %d\n head ", _tar); 
        while (pCrawl) 
        { 
            printf("-> %d", pCrawl->dest); 
            pCrawl = pCrawl->next; 
        } 
        printf("\n"); 
        */
      
        



        /*
            END FINDING ZONES:
        */

        /* ÎÎ°è²òÊü */
        free(area);
        free(sites);
        free(edge_sites);
        free(lineseg);
        free(graph);
        free(endp);
        freelist_destroy(&hfl);
        freelist_destroy(&efl);
        freelist_destroy(&sfl);

        printf("Done.\n");
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
        if((out_img->image=(char *)myalloc(in_img->imax*in_img->jmax))==NULL){
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

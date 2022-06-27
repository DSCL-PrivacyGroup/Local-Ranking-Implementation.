#include "stdio.h"
#include "string.h"
#include "stdlib.h"
#include "math.h"
#include "time.h"
#include <iostream>
#include <algorithm>
using namespace std;

#define M 1550
#define RN 250
#define RM 20

char tempstr[M];
char tempstr1[M];
char tempstr2[M];

char s[M];
int m;


typedef struct {
	int ta;
	int fr;
	int pr;
	int fa;
}Tes;

int subjects_number = 249;
int rm[RN];
char iris_codes[RN][RM][M];
char shift_codes[RN][RM][21][M];
char mask_codes[RN][RM][M];
int cmask[RN][RM][M];
int iris_code[RN][RM][M];
int shift_code[RN][RM][21][M];

double dist_EQ[RN][RM];
double dist_EQS[RN][RM];
double match_result[500000][3];
double avg_match_result[500000][3];
int FRM, END;
int rndv[RN];

char sdata[M], smask[M];
int scode[M];
int sindex_i, sindex_j;
int scmask[M];

double v[4][M];
int C = 0;
int SN = 17;   // The number shift code

int block_num;
int block_size;
int match_strategy;
char key[M];

bool flag[M];

int group_num = 32;
int group_size = 12;

void readfiles()
{
	int i, j, k;
	char filename[100];
	FILE* fp;
	m = 1536;
	for (i = 0; i < subjects_number; i++)
	{	
		for (j = 0; j <= RM; j++)
		{
			sprintf(filename, "Osiris\\binaryCode\\S1%03dL%02d.txt", i + 1, j + 1);
			fp = fopen(filename, "r");
			if (fp == NULL)
			{
				rm[i] = j;
				break;
			}
			fscanf(fp, "%s", iris_codes[i][j]);
			fscanf(fp, "%s", mask_codes[i][j]);
			fclose(fp);
		}
		for (j = 0; j < rm[i]; j++)
		{
			sprintf(filename, "Osiris\\shiftedBinaryCode\\S1%03dL%02d.txt", i + 1, j + 1);
			fp = fopen(filename, "r");
			for (k = 0; k < SN; k++)
			{
				fscanf(fp, "%s", shift_codes[i][j][k]);
			}
			fclose(fp);
		}
	}
}

void getRank(int val[], int ind[])
{   
	// Convert the decimal value to the corresponding ranking value in a group
	int i, j;
	int x[500];
	for (i = 0; i < group_size; i++) x[i] = val[i];
	sort(x, x + group_size);
	for (i = 0; i < group_size; i++)
	{
		flag[i] = 0;
	}
	for (i = 0; i < group_size; i++)
	{
		for (j = 0; j < group_size; j++)
		{
			if ((val[i] == x[j]) && (flag[j] == 0))
			{
				ind[i] = j;
				flag[j] = 1;
				break;
			}
		}
	}
}

void calculate_cmask()
{
	/*
	* Set the maskcode of the block to 1 as long as one bit of the mask in the block is 1
	*/
	int i, j, k, w, v;
	
	for (i = 0; i < subjects_number; i++)
	{
		for (j = 0; j < rm[i]; j++)
		{
			for (k = 0; k < block_num; k++)
			{
				int tag = 0;
				for (w = 0; w < block_size; w++)
				{
					int id = k * block_size + w;
					if (mask_codes[i][j][id] == '1') {
						cmask[i][j][k] = 1;
						tag = 1;
						break;
					}
				}
				if (tag == 0) {
					cmask[i][j][k] = 0;
				}
			}
		}
	}
}

void genKey()
{
	/*
	*  Initialize the Application-specific string p 
	*/
	int j, k;
	for (j = 0; j < block_num; j++)
	{
		for (k = 0; k < block_size; k++)
		{
			int id = j * block_size + k;
			key[id] = '0' + rand() % 2;
		}
	}
}

void localRank(char ir[], int cod[])
{
	/*
	* 1. Original xor with the rand key
	* 2. Convert the binary in every block to decimal value
	* 3. Sort within each group to get the ranking value
	*/

	int i, j;
	int val[500];
	int ind[500];

	for (i = 0; i < block_num; i++)
	{
		cod[i] = 0;
		int id = i * block_size;
		for (j = 0; j < block_size; j++)
		{
			cod[i] = cod[i] * 2 + fabs(ir[id + j] - key[id + j]);
		}
	}

	for (i = 0; i < group_num; i++)
	{
		int id = i * group_size;
		for (j = 0; j < group_size; j++)
		{
			val[j] = cod[id + j];
		}
		getRank(val, ind);
		for (j = 0; j < group_size; j++)
		{
			cod[id + j] = ind[j];
		}
	}
}

void dataset2Template()
{
	/*
	* Convert all the iris codes and shift codes to template
	*/
	int i, j, k;
	for (i = 0; i < subjects_number; i++)
	{
		for (j = 0; j < rm[i]; j++)
		{
			localRank(iris_codes[i][j], iris_code[i][j]);
			for (k = 0; k < SN; k++)
			{
				localRank(shift_codes[i][j][k], shift_code[i][j][k]);
			}
		}
	}
}

double EQ(int t[], int n)
{
	/*
	* basic matching strategy distance calculation
	*/
	int i;
	double dist = 0;
	for (i = 0; i < n; i++)
	{
		dist += fabs(scode[i] - t[i]);
	}
	return dist;
}

double EQ_shift(int t[], int n)
{	
	/*
	* shift code matching strategy distance calculation
	*/
	int i,j;
	double dist = 0;
	int min_dist = 1000000000;
	for(i=0;i<SN;i++)
	{
		dist = 0;
		for(j=0;j<n;j++)
		{
			dist +=fabs(shift_code[sindex_i][sindex_j][i][j]-t[j]);
		}
		if(dist < min_dist) min_dist = dist;
	}
	return min_dist;
}

double EQ_shift_mask(int t[], int scm[])
{
	/*
	* shift + mask matching strategy distance calculation
	*/
	int i,j,nv;
	int dist;
	double final_dist;
	int mask_len=0;
	int min_dist = 1000000000;
	for(i=0;i<SN;i++)
	{
		dist = 0;
		nv = 0;
		for(j=0;j<block_num;j++)
		{
			if ((scmask[j] == 1) && (scm[j] == 1)) {
				int tmp = fabs(shift_code[sindex_i][sindex_j][i][j] - t[j]);
				dist += tmp;
				nv++;         // maskLen of every shift code pair
			}
		}
		if (dist < min_dist) {
			min_dist = dist;
			mask_len = nv;
		}
	}
	if(mask_len == 0)
		final_dist =m/2;
	else
		final_dist =1.0*min_dist*block_num/ mask_len;
	return final_dist;
}

void distance_calculate()
{
	/*
	* calculate the distance according to different strategy
	*/
	int i, j;
	for (i = 0; i < subjects_number; i++)
	{
		for (j = 0; j < rm[i]; j++)
		{	
			// basic strategy
			if (match_strategy == 1) {
				dist_EQ[i][j] = EQ(iris_code[i][j], block_num);
			}
			// shift strategy 
			else if (match_strategy == 2) {
				dist_EQ[i][j] = EQ_shift(iris_code[i][j],block_num);
			}
			// shift and mask strategy
			else if (match_strategy == 3){
				dist_EQ[i][j] = EQ_shift_mask(iris_code[i][j],cmask[i][j]);
			}
		}
	}
}

void match()
{	
	/*
	* Intraclass and interclass template match
	*/ 
	int i, j;
	double fA, fR, tA, tR;

	distance_calculate();
	for (C = FRM; C < END; C++)
	{
		int ta = 0;   // true accept
		int fr = 0;   // false reject
		int fa = 0;   // false accept
		int tr = 0;   // true reject

		for (i = 0; i < subjects_number; i++)
		{
			for (j = 0; j < rm[i]; j++)
			{
				if (i == sindex_i)
				{
					if (dist_EQ[i][j] < C)
					{
						ta++;
					}
					else fr++;
				}
				else
				{
					if (dist_EQ[i][j] < C)
					{
						fa++;
					}
					else tr++;
				}
			}
		}

		if (fa + tr == 0) fA = 0;
		else
		{
			fA = 1.0 * fa / (fa + tr);
			tR = 1.0 * tr / (fa + tr);
		}
		if (fr + ta == 0) fR = 0;
		else
		{
			fR = 1.0 * fr / (fr + ta);
			tA = 1.0 * ta / (fr + ta);
		}
		match_result[C][0] += fA;
		match_result[C][1] += tA;
		match_result[C][2] += fR;
	}
}

void template_match()
{
	/*
	* Simulate the registered and identification process,
	* random select a data of subjects as the registered data,
	* the selected data is matched with intraclass and interclass.
	*/
	int i, j;
	int empty_number = 0;      // The subjects number without data
	int rnd = 0;     
	for (i = FRM; i < END; i++)
	{
		match_result[i][0] = 0;
		match_result[i][1] = 0;
		match_result[i][2] = 0;
	}

	for (i = 0; i < subjects_number; i++)
	{
		if (rm[i] == 0)
		{
			empty_number++;
			continue;
		}
		rnd = rand() % rm[i];   // Randomly select one as the registration data
		for (j = 0; j < m; j++)
		{
			sdata[j] = iris_codes[i][rnd][j];
			smask[j] = mask_codes[i][rnd][j];
		}
		for (j = 0; j < block_num; j++)
		{
			scode[j] = iris_code[i][rnd][j];
			scmask[j] = cmask[i][rnd][j];
		}
		sindex_i = i;    // user id
		sindex_j = rnd; 
		match();
	}

	for (i = FRM; i < END; i++)
	{
		match_result[i][0] = match_result[i][0] / (subjects_number - empty_number);
		match_result[i][1] = match_result[i][1] / (subjects_number - empty_number);
		match_result[i][2] = match_result[i][2] / (subjects_number - empty_number);
	}
	printf("\n");
}

void main_process()
{
	/*
	* 1. Input and initialize the parameters
	* 2. Call the key generation, template transformation, and template matching interfaces
	* 3. Save the template match result
	*/
	FILE* fp;
	int iterN = 30;
	char filename[100];
	printf("Please input the block_size and group_size:");
	scanf("%d %d", &block_size, &group_size);
	printf("Please input match strategy(1.basic; 2.shift; 3.shift+mask):");
	scanf("%d", &match_strategy);
	sprintf(filename, "EQ_matchStrategy=%d_b=%d_d=%d.txt", match_strategy,block_size, group_size);
	fp = fopen(filename, "w");

	block_num = m / block_size;
	group_num = block_num / group_size;

	FRM = 0;
	END = FRM + 8 * m;
	for (C = FRM; C < END; C++)
	{
		avg_match_result[C][0] = 0;
		avg_match_result[C][1] = 0;
		avg_match_result[C][2] = 0;
	}

	calculate_cmask();

	for (int i = 0; i < iterN; i++)
	{
		printf("\n\n\n------------------------------ %d-th process -------------------------------\n", i+1);
		genKey();
		dataset2Template();
		template_match();
		for (C = FRM; C < END; C++)
		{
			avg_match_result[C][0] += match_result[C][0] / iterN;
			avg_match_result[C][1] += match_result[C][1] / iterN;
			avg_match_result[C][2] += match_result[C][2] / iterN;
		}
		for (C = FRM; C < END; C++)
		{
			printf("%lf/%lf/%lf ", match_result[C][0], match_result[C][1],match_result[C][2]);
		}
	}
	for (int i = FRM; i < END; i++)
	{
		fprintf(fp, "%d %lf %lf %lf\n", i, avg_match_result[i][0], avg_match_result[i][1], avg_match_result[i][2]);
	}
	fclose(fp);
}

int main()
{
	srand((unsigned)(time(0)));
	m = 1536;
	readfiles();
	main_process();
	return 0;
}
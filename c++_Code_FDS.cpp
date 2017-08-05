


#include <iostream>
#include <fstream>
#include <math.h>
#include "llvm/Pass.h"
#include "llvm/Analysis/CFGPrinter.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/InstIterator.h"
//#include "SelectionDAGNodes.h"
#include "llvm/CodeGen/SelectionDAG.h"
#include "llvm/CodeGen/MachineFunction.h"

using namespace llvm;


std::ofstream out("result.txt");
typedef std::string string;
int Latency;
/* Item is the data structure to hold info about each operation */
struct Item
{
	std::string name;
	char * type;
	int NoOfOperands;
	std::vector<std::string> OperandList;
	std::vector<std::string> UserList;
	char * Scheduled;
	std::string FDS_Scheduled = "NO";
	int FDS_start=0;
	int ASAP_start=0;
	int ALAP_start=1000;
};

std::map<std::string,Item *> AdjustPredTimeframes(std::map<std::string,Item *>,Item *);
std::map<std::string,Item *> AdjustSuccTimeframes(std::map<std::string,Item *>,Item *);

/* Function to increase the Time Frame of each operation by extending the ALAP Time*/

std::map<string,Item *> RelaxLatency(std::map<string,Item *> List,int Old,int New)/*takes map of instructions, old and new latencies as imput, returns new map of instructions*/
{

	int change=New-Old;
	for(std::map<string,Item *>::iterator iter = List.begin(); iter != List.end(); ++iter)
	{
		iter->second->ALAP_start=iter->second->ALAP_start+change;

	}
	return List;
}
/* Function to Distribution graph of all cycles*/
std::vector<float> CalculateDG(std::map<string,Item *> List) /*takes map of instructions as input, returns a floating point vector */
{

	std::vector<float> DG;
	int i=0;
	int NumberCycles;
	Item * ptr;
	for(i=0;i<Latency;i++)
		DG.push_back(0.0);//creating empty DG
	for(std::map<string,Item *>::iterator iter = List.begin(); iter != List.end(); iter++)
	{
		ptr=iter->second;
		if(ptr->UserList.size()==0)
			continue;
		else
		{
			int ASAP_time,ALAP_time,Max_time;
			float max_avg=0.0;
			float Avg_Life,contribution,max_life;
			int overlap=0;
			struct Item * max_user;
			struct Item * succ_ptr;
			string succ;
			for(int i=0;i<ptr->UserList.size();i++)
			{
				succ=ptr->UserList[i];
				if(List.find(succ)==List.end())
					continue;
				succ_ptr=List[succ];
				ASAP_time=succ_ptr->ASAP_start-ptr->ASAP_start;
				ALAP_time=succ_ptr->ALAP_start-ptr->ALAP_start;
				Max_time=succ_ptr->ALAP_start-ptr->ASAP_start;
				Avg_Life=(float)((float)(ASAP_time+ALAP_time+Max_time)/3);//calculating avg life
				if(Avg_Life>=max_avg)
				{
					max_avg=Avg_Life;
					max_user=succ_ptr;
					if(succ_ptr->ASAP_start>ptr->ALAP_start)						
						overlap=succ_ptr->ASAP_start-ptr->ALAP_start-1;//calculating overlap if any
				}
			}
			ASAP_time=max_user->ASAP_start-ptr->ASAP_start;
			ALAP_time=max_user->ALAP_start-ptr->ALAP_start;
			max_life=max_user->ALAP_start-ptr->ASAP_start;
			Avg_Life=(float)((float)(ASAP_time+ALAP_time+Max_time)/3);
			contribution=(float)((float)(max_avg-overlap)/(float)(max_life-overlap));

			if(max_user->ASAP_start>ptr->ALAP_start)

				overlap=max_user->ASAP_start-ptr->ALAP_start-1;

			for(int j=ptr->ASAP_start;j<max_user->ASAP_start;j++)
			{

				if(j>=ptr->ALAP_start+1 && j<max_user->ASAP_start+1)
					DG[j]=DG[j]+1;//if in overlapped cycles,contribution is 1                    
				else 
					DG[j]=DG[j]+contribution;//in non-overlapping cycles, contribution is added
			}		

		}

	}

	return DG;
}

//Function to calculate force of a an operation ptr in cycle 'step'
float CalculateSelfForce(std::map<string,Item *> ListInstructions,Item * ptr,int step )

{
	std::map<string,Item *> ListCopy;	
	Item * t;
	for(std::map<string,Item *>::iterator iter = ListInstructions.begin(); iter != ListInstructions.end(); iter++)
	{				
		if(iter->second)
		{
			struct Item * temp;
			temp=(Item *)new Item;
			*temp=*(iter->second);
			ListCopy[temp->name]=temp;
		}


	}/*creating copy of map , so that operations can be pseudo-scheduled without affecting original map*/
	t=ListCopy[ptr->name];
	ListCopy[ptr->name]->ASAP_start=step;
	ListCopy[ptr->name]->ALAP_start=step;//scheduling in step 
	ListCopy=AdjustPredTimeframes(ListCopy,t);
	ListCopy=AdjustSuccTimeframes(ListCopy,t);//adjusting pred and succ time frames
	std::vector<float> DG;
	Item * pred_ptr, * succ_ptr;
	DG=CalculateDG(ListCopy);//recalculating Distribution Graph
	int pred_avail,last_needed,time,NumberOfCycles;
	int earliest_start=ListCopy[ptr->name]->ASAP_start;
	string pred,succ;
	if(ptr->OperandList.size()==0)
		pred_avail=ListCopy[ptr->name]->ASAP_start;
	else
	{
		for(int i=0;i<ptr->OperandList.size();i++)
		{
			pred=ptr->OperandList[i];
			if(ListCopy.find(pred)==ListCopy.end())
				continue;
			pred_ptr=ListCopy[pred];
			if(pred_ptr->FDS_Scheduled=="YES")
			{
				if(pred_ptr->ASAP_start<earliest_start)
					earliest_start=pred_ptr->ASAP_start+1;
			}
			else
			{
				time=ceil((pred_ptr->ASAP_start+pred_ptr->ALAP_start)/2);
				if(time<earliest_start)
					earliest_start=time;
			}

		}
		pred_avail=earliest_start;// Predecessor with the earliest start time
	}
	if(ptr->UserList.size()==0)
		last_needed=ListCopy[ptr->name]->ALAP_start;
	else
	{
		int latest_start=ListCopy[ptr->name]->ALAP_start;
		for(int i=0;i<ptr->UserList.size();i++)
		{
			succ=ptr->UserList[i];
			if(ListCopy.find(succ)==ListCopy.end())
				continue;					
			succ_ptr=ListCopy[succ];
			if(succ_ptr->FDS_Scheduled=="YES")
			{
				if(succ_ptr->ASAP_start>latest_start)
					latest_start=succ_ptr->ASAP_start+1;
			}
			else
			{
				time=ceil((succ_ptr->ASAP_start+succ_ptr->ALAP_start)/2);
				if(time>latest_start)
					latest_start=time;
			}
		}
		last_needed=latest_start;//User with the farthest start time
	}
	NumberOfCycles=last_needed-pred_avail;
	float NewSum=0.0;
	for(int k=pred_avail;k<last_needed;k++)
		NewSum+=DG[k];

	float DG_ALL=0.0;
	/*Calculating force in all other cycles in operations time frame*/
	for(int h=ptr->ASAP_start;h<ptr->ALAP_start+1;h++)
	{
		std::map<string,Item *> ListCopy2;
		Item * t1;
		for(std::map<string,Item *>::iterator iter = ListInstructions.begin(); iter != ListInstructions.end(); ++iter)
		{
			if(iter->second)
			{
				struct Item * temp;
				temp=(Item *)new Item;
				*temp=*(iter->second);
				ListCopy2[temp->name]=temp;
			}
		}
		t1=ListCopy2[ptr->name];
		ListCopy2[ptr->name]->ASAP_start=h;
		ListCopy2[ptr->name]->ALAP_start=h;
		ListCopy2=AdjustPredTimeframes(ListCopy2,t1);
		ListCopy2=AdjustSuccTimeframes(ListCopy2,t1);
		std::vector<float> DG_Mod;
		DG_Mod=CalculateDG(ListCopy2);
		float New_Sum_Step=0.0;
		int pred_avail2,last_needed2,time2,NumberOfCycles2;
		int earliest_start2=ListCopy2[ptr->name]->ASAP_start;
		if(ptr->OperandList.size()==0)
			pred_avail2=ListCopy2[ptr->name]->ASAP_start;
		else
		{
			for(int i=0;i<ptr->OperandList.size();i++)
			{
				pred=ptr->OperandList[i];
				if(ListCopy2.find(pred)==ListCopy2.end())
					continue;
				pred_ptr=ListCopy2[pred];
				if(pred_ptr->FDS_Scheduled=="YES")
				{
					if(pred_ptr->ASAP_start<earliest_start2)
						earliest_start2=pred_ptr->ASAP_start+1;
				}
				else
				{
					time2=ceil((pred_ptr->ASAP_start+pred_ptr->ALAP_start)/2);
					if(time2<earliest_start2)
						earliest_start2=time2;
				}
			}
			pred_avail2=earliest_start2;
		}

		if(ptr->UserList.size()==0)
			last_needed2=ListCopy2[ptr->name]->ALAP_start;
		else
		{
			int latest_start2=ListCopy2[ptr->name]->ALAP_start;
			for(int i=0;i<ptr->UserList.size();i++)
			{
				succ=ptr->UserList[i];
				if(ListCopy2.find(succ)==ListCopy2.end())
					continue;
				succ_ptr=ListCopy2[succ];
				if(succ_ptr->FDS_Scheduled=="YES")
				{
					if(succ_ptr->ASAP_start>latest_start2)
						latest_start2=succ_ptr->ASAP_start+1;
				}
				else
				{								
					time2=ceil((succ_ptr->ASAP_start+succ_ptr->ALAP_start)/2);
					if(time2>latest_start2)
						latest_start2=time2;
				}

			}
			last_needed2=latest_start2;
		}		
		for(int y=pred_avail2;y<last_needed2;y++)
			New_Sum_Step+=DG_Mod[y];
		DG_ALL+=New_Sum_Step;
	}
	int ncycles=ListCopy[ptr->name]->ALAP_start-ListCopy[ptr->name]->ALAP_start+1;
	float self_force_a;
	self_force_a=NewSum-(float)((float)DG_ALL/ncycles);
	return self_force_a;
}
/* Function to print results out onto a text file*/

void PrintResults(std::map<string,Item *> List)
{

	int reg_count,max_reg;
	Item * succ_ptr;
	string succ;
	max_reg=0;
	out<<"\n\n\n\n SCHEDULE ASAP LATENCY IS"<<Latency;
	for(int n=0;n<Latency;n++)
	{
		out<<"\n CYCLE "<<n+1;
		int reg_stage=0;
		for(std::map<string,Item *>::iterator iter = List.begin(); iter != List.end(); iter++)
		{
			if(iter->second->ASAP_start==n)
				out<<"\n"<<iter->first;
			if(iter->second->ASAP_start<=n)
			{
				int max_succ=0;
				for(int i=0;i<iter->second->UserList.size();i++)
				{

					succ=iter->second->UserList[i];
					if(List.find(succ)==List.end())
						continue;
					succ_ptr=List[succ];
					if(succ_ptr->ASAP_start>max_succ)
						max_succ=succ_ptr->ASAP_start;
				}
				if(max_succ>n)
					reg_stage++;
			}
		}

		out<<"\n \n REG COUNT STAGE "<<n+1<<" is"<<reg_stage;
		out<<"\n --------------------";
		if(reg_stage>max_reg)
			max_reg=reg_stage;
	}

	out<<"\n\ \n\ max_reg"<<max_reg;

}

/* Function to print results out onto a text file*/
void PrintResults_ALAP(std::map<string,Item *> List)

{

	int reg_count,max_reg;
	Item * succ_ptr;
	string succ;
	max_reg=0;
	out<<"\n\n\n\n SCHEDULE ALAP LATENCY IS"<<Latency;
	for(int n=0;n<Latency;n++)
	{

		out<<"\n CYCLE "<<n+1;
		int reg_stage=0;
		for(std::map<string,Item *>::iterator iter = List.begin(); iter != List.end(); iter++)
		{

			if(iter->second->ALAP_start==n)
				out<<"\n"<<iter->first;
			if(iter->second->ALAP_start<=n)
			{
				int max_succ=0;
				for(int i=0;i<iter->second->UserList.size();i++)
				{
					succ=iter->second->UserList[i];
					if(List.find(succ)==List.end())
						continue;
					succ_ptr=List[succ];
					if(succ_ptr->ALAP_start>max_succ)
						max_succ=succ_ptr->ALAP_start;
				}

				if(max_succ>n)
					reg_stage++;

			}
		}

		out<<"\n \n REG COUNT STAGE "<<n+1<<" is"<<reg_stage;
		out<<"\n --------------------";
		if(reg_stage>max_reg)
			max_reg=reg_stage;
	}

	out<<"\n\ \n\ max_reg"<<max_reg;

}



/* Function to print results out onto a text file*/
void PrintResultsFDS(std::map<string,Item *> List)
{

	int reg_count,max_reg;
	Item * succ_ptr;
	string succ;
	max_reg=0;
	out<<"\n\n\n\n SCHEDULE FDS LATENCY IS"<<Latency;
	for(int n=0;n<Latency;n++)
	{
		out<<"\n CYCLE "<<n+1;
		int reg_stage=0;
		for(std::map<string,Item *>::iterator iter = List.begin(); iter != List.end(); iter++)
		{
			if(iter->second->FDS_start==n)
				out<<"\n"<<iter->first;
			if(iter->second->FDS_start<=n)
			{
				int max_succ=0;
				for(int i=0;i<iter->second->UserList.size();i++)
				{
					succ=iter->second->UserList[i];
					if(List.find(succ)==List.end())
						continue;
					succ_ptr=List[succ];
					if(succ_ptr->FDS_start>max_succ)
						max_succ=succ_ptr->FDS_start;
				}

				if(max_succ>n)
					reg_stage++;
			}


		}
		out<<"\n \n REG COUNT STAGE "<<n+1<<" is"<<reg_stage;
		out<<"\n --------------------";
		if(reg_stage>max_reg)
			max_reg=reg_stage;
	}

	out<<"\n\ \n\ max_reg"<<max_reg;

}


/*calculating change in force of predecessor*/
float CalcPredChangeInForce(std::map<string,Item *> ListInstructions,Item * ptr,float val)

{

	float change_in_pred_force=val;
	std::vector<float> DG_mod=CalculateDG(ListInstructions);
	int step=ptr->ASAP_start;
	string curr_pred,preds_pred;
	Item * pred_ptr;
	if(ptr->OperandList.empty()!=1)
	{	

		for(int i=0;i<ptr->OperandList.size();i++)
		{
			curr_pred=ptr->OperandList[i];
			if(ListInstructions.find(curr_pred)==ListInstructions.end())
				continue;
			pred_ptr=ListInstructions[curr_pred];
			if(pred_ptr->FDS_Scheduled=="NO" && pred_ptr->ALAP_start>=step)
			{

				float old_val=0.0;
				float new_val=0.0;
				int old_time_frame,new_time_frame;
				old_time_frame=pred_ptr->ALAP_start-pred_ptr->ASAP_start+1;
				new_time_frame=step-pred_ptr->ASAP_start+1;
				for(int i=pred_ptr->ASAP_start;i<=pred_ptr->ALAP_start;i++)
					old_val=old_val+DG_mod[i];
				old_val=old_val/old_time_frame;
				for(int i=pred_ptr->ASAP_start;i<=step;i++)
					new_val=new_val+DG_mod[i];
				new_val=new_val/new_time_frame;
				change_in_pred_force=val+new_val-old_val;
				Item * preds_pred;
				if(pred_ptr->OperandList.empty()!=1)

					change_in_pred_force=CalcPredChangeInForce(ListInstructions,pred_ptr,change_in_pred_force);

			}
		}		
	}
	return change_in_pred_force;
}


/*calculating change in force of successor*/
float CalcSuccChangeInForce(std::map<string,Item *> ListInstructions,Item * ptr,float val)

{
	float change_in_succ_force=val;
	std::vector<float> DG_mod=CalculateDG(ListInstructions);
	int step=ptr->ASAP_start;
	string curr_succ,succs_succ;
	Item * succ_ptr;
	if(ptr->UserList.empty()!=1)
	{
		for(int i=0;i<ptr->UserList.size();i++)
		{
			curr_succ=ptr->UserList[i];
			if(ListInstructions.find(curr_succ)==ListInstructions.end())
				continue;
			succ_ptr=ListInstructions[curr_succ];
			if(succ_ptr->FDS_Scheduled=="NO" && succ_ptr->ASAP_start<=step)
			{
				float old_val=0.0;
				float new_val=0.0;
				int old_time_frame,new_time_frame;
				old_time_frame=succ_ptr->ALAP_start-succ_ptr->ASAP_start+1;
				new_time_frame=succ_ptr->ALAP_start-step+1;
				for(int i=succ_ptr->ASAP_start;i<=succ_ptr->ALAP_start;i++)
					old_val=old_val+DG_mod[i];
				old_val=old_val/old_time_frame;
				for(int i=succ_ptr->ASAP_start;i<=step;i++)
					new_val=new_val+DG_mod[i];
				new_val=new_val/new_time_frame;
				change_in_succ_force=val+new_val-old_val;
				Item * succs_succ;
				if(succ_ptr->UserList.empty()!=1)
					change_in_succ_force=CalcSuccChangeInForce(ListInstructions,succ_ptr,change_in_succ_force);

			}
		}		
	}
	return change_in_succ_force;
}


/*Function to calculate and return pred/succ forces*/
float CalcPredSuccForce(std::map<string,Item *> ListInstructions,Item * ptr,int step)
{

	std::map<string,Item *> ListCopy;
	Item * t;
	for(std::map<string,Item *>::iterator iter = ListInstructions.begin(); iter != ListInstructions.end(); ++iter)
	{
		if(iter->second)
		{
			struct Item * temp;
			temp=(Item *)new Item;
			*temp=*(iter->second);
			ListCopy[temp->name]=temp;
		}
	}

	ListCopy[ptr->name]->ASAP_start=step;
	ListCopy[ptr->name]->ALAP_start=step;
	t=ListCopy[ptr->name];
	float  Change_in_Force_Pred=0.0;
	float  Change_in_Force_Succ=0.0;
	float Total_Change=0.0;
	Change_in_Force_Pred=CalcPredChangeInForce(ListCopy,t,0.0);
	Change_in_Force_Succ=CalcSuccChangeInForce(ListCopy,t,0.0);
	Total_Change=Change_in_Force_Succ+Change_in_Force_Pred;
	return Total_Change;
}


/*Function to adjust the timeframes of predecessors of operation ptr once it has been scheduled*/
std::map<string,Item *> AdjustPredTimeframes(std::map<string,Item *> List,Item * ptr)
{
	string pred;
	Item * pred_ptr;
	if(ptr->OperandList.size()==0)
		return List;//no preds, no need to adjust
	else
	{
		for(int i=0;i<ptr->OperandList.size();i++)
		{
			pred=ptr->OperandList[i];
			if(pred==ptr->name)
				continue;
			if(List.find(pred)!=List.end())
			{
				pred_ptr=List[pred];
				if(pred_ptr->FDS_Scheduled=="NO" && pred_ptr->ALAP_start>=ptr->ALAP_start)
					List[pred]->ALAP_start=ptr->ALAP_start-1;//adjust ALAP time of pred
			}					
		}				
		if(ptr->OperandList.size()==1)
		{
			pred=ptr->OperandList[0];

			if(List.find(pred)!=List.end())
			{
				pred_ptr=List[pred];
				List=AdjustPredTimeframes(List,pred_ptr);//recursively adjust predecessor's predecessor
			}
			return List;

		}			 
		if(ptr->OperandList.size()>=2)
		{
			pred=ptr->OperandList[1];
			if(pred==ptr->name)
				pred="&%^%&^";
			string pred2;
			Item * pred_ptr2;
			pred2=ptr->OperandList[0];
			if(pred2==ptr->name)
				pred2=="*^&^&";
			if(List.find(pred)!=List.end() && List.find(pred2)!=List.end())
			{
				pred_ptr=List[pred];
				pred_ptr2=List[pred2];
				List=AdjustPredTimeframes(List,pred_ptr);
				List=AdjustPredTimeframes(List,pred_ptr2);
			}

			else if(List.find(pred)!=List.end() && List.find(pred2)==List.end())
			{
				pred_ptr=List[pred];
				List=AdjustPredTimeframes(List,pred_ptr);
			}

			else if(List.find(pred)==List.end() && List.find(pred2)!=List.end())
			{
				pred_ptr2=List[pred2];
				List=AdjustPredTimeframes(List,pred_ptr2);
			}
			return List;					
		}		
	}
	return List;	
}


/* Function to adjust successor's time frame*/
std::map<string,Item *> AdjustSuccTimeframes(std::map<string,Item *> List,Item * ptr)
{

	string succ;
	Item * succ_ptr;
	int step=ptr->ASAP_start;
	if(ptr->UserList.size()==0)
		return List;//No successor, no need to adjust
	for(int i=0;i<ptr->UserList.size();i++)
	{
		succ=ptr->UserList[i];
		if(List.find(succ)==List.end())
			continue;
		succ_ptr=List[succ];
		if(succ_ptr->FDS_Scheduled=="NO" && succ_ptr->ASAP_start<=step)
			List[succ_ptr->name]->ASAP_start=step+1;//adjusting ASAP time of successor
	}
	for(int i=0;i<ptr->UserList.size();i++)
	{
		if(ptr->UserList.size()==1)
		{
			succ=ptr->UserList[0];
			if(List.find(succ)!=List.end())
			{
				succ_ptr=List[succ];
				List=AdjustSuccTimeframes(List,succ_ptr);
			}				
			return List;
		}
	}
	/*recursively adjusting successor's successors*/
	for(int i=0;i<ptr->UserList.size();i++)
	{
		if(ptr->UserList.size()==2)
		{
			string succ2;
			Item * succ_ptr2;
			succ=ptr->UserList[1];
			succ2=ptr->UserList[0];
			if(List.find(succ)!=List.end() && List.find(succ2)!=List.end() )
			{
				succ_ptr=List[succ];
				succ_ptr2=List[succ2];
				List=AdjustSuccTimeframes(List,succ_ptr);
				List=AdjustSuccTimeframes(List,succ_ptr2);
			}
			else if(List.find(succ)==List.end() && List.find(succ2)!=List.end() )
			{
				succ_ptr2=List[succ2];
				List=AdjustSuccTimeframes(List,succ_ptr2);
			}
			else if(List.find(succ2)==List.end() && List.find(succ)!=List.end())
			{
				succ_ptr=List[succ];
				List=AdjustSuccTimeframes(List,succ_ptr);
			}
			return List;
		}		

	}

	return List;
}

struct Item * NewItem;
namespace{

	std::map<string,Item *> ListInstructions;
	struct PrintInst : public FunctionPass {
		static char ID;
		PrintInst() : FunctionPass(ID){}

		virtual bool runOnFunction(Function& F)
		{
			std::vector<Instruction*> worklist;
			BasicBlock * blk;  
			/*adding instructions from file to worklist, a vector that holds items of type Instruction **/
			for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I)
				worklist.push_back(&*I);

			for(std::vector<Instruction*>::iterator iter = worklist.begin(); iter != worklist.end(); ++iter){
				Instruction* instr = *iter;  
				User* u=*iter;
				Value* v=*iter;				
				if((instr->getName().empty() || instr->getNumOperands()==0) && instr->mayReadOrWriteMemory()==0)
				{
					continue;
				} /* movning to next item if item is a constant*/
				string NameStore;/*creating a data struct of type item for each operation to store its details*/
				NewItem= (Item *)new Item;
				if(instr->mayReadOrWriteMemory())
				{


					std::string str;
					llvm::raw_string_ostream rso(str);
					instr->print(rso);
					string NameStore;
					NameStore=rso.str();
					int pos1=NameStore.find('@');
					string NameStore2=NameStore.substr(pos1+1);
					int pos2=NameStore2.find(',');
					string NameStore3=NameStore2.substr(0,pos2);
					NewItem->name=NameStore3;
				}
				else
					NewItem->name=instr->getName();
				NewItem->type=(char *)instr->getOpcodeName();
				NewItem->NoOfOperands=instr->getNumOperands();
				NewItem->Scheduled="No";
				NewItem->ASAP_start=0;
				NewItem->ALAP_start=0;
				int NumOperands;
				NumOperands=instr->getNumOperands();
				for(int m=0;m<NumOperands;m++)
					NewItem->OperandList.push_back(((instr->getOperand(m))->getName()));/*adding operands ot each instruction to list*/

				for(Value::use_iterator iter_use=instr->use_begin();iter_use!=instr->use_end();++iter_use)
				{
					string name_op;						
					if(Instruction* instr1=dyn_cast<Instruction>(*iter_use))
					{						
						if(instr1->mayReadOrWriteMemory())
						{					
							std::string str;
							llvm::raw_string_ostream rso(str);
							instr1->print(rso);
							string NameStore;
							NameStore=rso.str();
							int pos1=NameStore.find('@');
							string NameStore2=NameStore.substr(pos1+1);
							int pos2=NameStore2.find(',');
							string NameStore3=NameStore2.substr(0,pos2);
							name_op=NameStore3;
						}
						else
							name_op=instr1->getName();
					}
					NewItem->UserList.push_back(name_op);/*adding users of each instruction*/
				}
				ListInstructions[NewItem->name]=(NewItem);				
			}			
			int step=0;		

			/*ASAP schedule */
			for(std::vector<Instruction*>::iterator iteri = worklist.begin(); iteri != worklist.end(); iteri++)
			{				
				Instruction* instr = *iteri;
				if((instr->getName().empty() || instr->getNumOperands()==0) && instr->mayReadOrWriteMemory()==0)
					continue;
				Item * iter;
				string nameop;
				if(instr->mayReadOrWriteMemory())
				{

					std::string str;
					llvm::raw_string_ostream rso(str);
					instr->print(rso);
					string NameStore;
					NameStore=rso.str();
					int pos1=NameStore.find('@');
					string NameStore2=NameStore.substr(pos1+1);
					int pos2=NameStore2.find(',');
					string NameStore3=NameStore2.substr(0,pos2);
					nameop=NameStore3;
				}
				else
					nameop=instr->getName();


				iter=ListInstructions[nameop];
				struct Item * temp, * temp2, * temp3, * temp4;
				temp=iter;				
				int x=0;
				int val=9999;
				int found=0;		
				int max_pred=0;
				found=0;
				for(x=0;x<temp->NoOfOperands;x++)
				{					
					for(std::map<string,Item *>::iterator iter2 = ListInstructions.begin(); iter2 != ListInstructions.end(); iter2++)
					{
						temp3=iter2->second;						
						if(temp3->name==temp->OperandList[x] && temp->OperandList[x].empty()!=1 ){
							found=1;					
							if(temp3->ASAP_start>max_pred)
								max_pred=temp3->ASAP_start;			
						}
					}
				}					
				if(found)
				{				
					val=0;
					if(max_pred>=val)
						val=max_pred;
					else
						val=0;			

				}
				if(val==0)
					temp->ASAP_start=val+1;
				else if(val==9999)
					temp->ASAP_start=step;
				else

					temp->ASAP_start=val+1;
				if(temp->ASAP_start>Latency)
					Latency=temp->ASAP_start;
			}
			Latency=1;
			Item * assign;
			for(std::map<string,Item *>::iterator iter1 = ListInstructions.begin(); iter1 != ListInstructions.end(); ++iter1)
			{
				assign=iter1->second;
				assign->ALAP_start=Latency;
			}
			/*ALAP schedule*/
			for(std::vector<Instruction*>::iterator iteri = worklist.end()-1; iteri != worklist.begin()-1; --iteri)
			{			
				Instruction* instr = *iteri;
				if((instr->getName().empty() || instr->getNumOperands()==0) && instr->mayReadOrWriteMemory()==0)
					continue;
				Item * iter;
				string nameop;
				if(instr->mayReadOrWriteMemory())
				{
					std::string str;
					llvm::raw_string_ostream rso(str);
					instr->print(rso);
					string NameStore;
					NameStore=rso.str();
					int pos1=NameStore.find('@');
					string NameStore2=NameStore.substr(pos1+1);
					int pos2=NameStore2.find(',');
					string NameStore3=NameStore2.substr(0,pos2);
					nameop=NameStore3;
				}
				else
					nameop=instr->getName();
				Item * iter_alap;
				iter_alap=ListInstructions[nameop];
				int found=0;
				int val=Latency;
				int min_succ=Latency-1;
				struct Item * temp_alap,* temp3,* temp4,* temp2;
				temp_alap=iter_alap;
				if(temp_alap->ASAP_start==Latency-1)
					temp_alap->ALAP_start=Latency-1;
				int NoOfUsers=temp_alap->UserList.size();
				if(NoOfUsers==0)
				{
					temp_alap->ALAP_start=Latency-1;
					continue;
				}
				found=0;
				for(int x=0;x<NoOfUsers;x++)
				{					
					for(std::map<string,Item *>::iterator iter8 = ListInstructions.begin(); iter8 != ListInstructions.end(); ++iter8)
					{
						temp3=iter8->second;					
						if(temp3->name==temp_alap->UserList[x] && temp_alap->UserList[x].empty()!=1 ){
							found=1;
							if(temp3->ALAP_start<=min_succ)
								min_succ=temp3->ALAP_start;

						}

					}
				}				
				if(found)
					temp_alap->ALAP_start=min_succ-1;
			}

			PrintResults(ListInstructions);
			PrintResults_ALAP(ListInstructions);
			ListInstructions=RelaxLatency(ListInstructions,Latency,Latency);
			Latency=Latency;		
			int NumberInst=ListInstructions.size();

			/*FDS STARTS*/
			while(NumberInst>0)/* while not all instructions are scheduled*/
			{
				float minforce=999999.0;
				int modified=0;
				int step_scheduled;
				string inst_to_schedule;
				/*iterate over all instructions*/
				for(std::map<string,Item *>::iterator iter = ListInstructions.begin(); iter != ListInstructions.end(); iter++)
				{					
					if(iter->second->FDS_Scheduled=="NO")
					{						
						int a=iter->second->ASAP_start;
						int b=iter->second->ALAP_start;
						if(a==b)/*if time frame reduced to one cycle by adjustments, schedule*/
						{
							/*scheduling*/
							iter->second->FDS_start=a;
							iter->second->FDS_Scheduled="YES";
							NumberInst=NumberInst-1;
							iter->second->ASAP_start=a;
							iter->second->ALAP_start=a;
							iter->second->FDS_start=a;
							/*adjusting pred succ*/
							ListInstructions=AdjustPredTimeframes(ListInstructions,iter->second);
							ListInstructions=AdjustSuccTimeframes(ListInstructions,iter->second);

						}
						else
						{
							/*Force Calc*/
							int l;
							int start,end;
							start=iter->second->ASAP_start;
							end=iter->second->ALAP_start;						
							for(l=start;l<=end;l=l+1)/*For each cycle in time frame of instruction*/
							{								
								float Self_Force=0.0;
								float Total_Force=0.0;								
								Self_Force=CalculateSelfForce(ListInstructions,iter->second,l);									
								float Pred_Succ_Forces=0.0;								
								Total_Force=Self_Force+Pred_Succ_Forces;								
								if(Total_Force<minforce)
								{									
									modified=1;
									minforce=Total_Force;
									step_scheduled=l;
									inst_to_schedule=iter->first;

								}
							}
						}
					}
				}
				if(modified==1)/*min force instruction found*/
				{
					/*scheduling*/
					ListInstructions[inst_to_schedule]->FDS_start=step_scheduled;
					ListInstructions[inst_to_schedule]->FDS_Scheduled="YES";				
					ListInstructions[inst_to_schedule]->ASAP_start=step_scheduled;
					ListInstructions[inst_to_schedule]->ALAP_start=step_scheduled;				
					Item * temp;
					temp=ListInstructions[inst_to_schedule];				
					ListInstructions=AdjustPredTimeframes(ListInstructions,temp);
					ListInstructions=AdjustSuccTimeframes(ListInstructions,temp);				
					NumberInst=NumberInst-1;
				}
			}			
			float Self_Force=0.0;			
			PrintResultsFDS(ListInstructions);
			out.close();
			return false;
		}
	};
}	
char PrintInst::ID = 0;
static RegisterPass<PrintInst> X("rcs", "REGISTER CONSTRAINT SCHEDULING", false, false);

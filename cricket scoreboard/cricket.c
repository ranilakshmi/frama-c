struct Over{
    int over_number;
    int balls_bowled;
    char bowler[50];
    int runs_scored;
    int num_extras;
    int wickets;
};
struct Over over;
/*@
    requires over.runs_scored < 10000 && over.runs_scored >=0;
    requires over.num_extras <10000 && over.num_extras>=0;
    requires over.wickets < 11 && over.wickets >=0;
    requires over.balls_bowled < 50 && over.balls_bowled >=0;
    requires 0<=wkt <=1 && 0<=runs<=7 && 0<=extras<=5;
    ensures over.runs_scored == \old(over.runs_scored)+ runs + extras;
    ensures over.num_extras == \old(over.num_extras) + extras;
    ensures over.wickets == \old(over.wickets) + wkt;
    ensures over.balls_bowled == \old(over.balls_bowled) +1;
*/
void update_over(int runs,int extras,int wkt){
    over.runs_scored = over.runs_scored+ runs + extras;
    over.num_extras += extras;
    over.wickets += wkt;
    over.balls_bowled ++;
}
struct Bowler{
    char name[10];
    int overs_bowled;
    int balls_bowled;
    int wickets;
    int extras;
    //int runs_conceded;
    //float economy;
};
struct Bowler b;
/*@
    requires 0 <= b.overs_bowled <= 10 ;
    requires 0 <= b.balls_bowled <= 100;
    requires 0 <= b.wickets <= 10;
    requires 0 <= b.extras <= 40;
    requires 0 <= wkt <=1 && 0<= extras <=5;
    ensures b.balls_bowled == \old(b.balls_bowled) + 1;
    ensures b.wickets == \old(b.wickets) + wkt;
    ensures b.extras == \old(b.extras) + extras;
    ensures b.overs_bowled == (b.balls_bowled) / 6;

*/
void update_bowler(int wkt,int extras){
    b.balls_bowled ++ ;
    b.wickets = b.wickets + wkt;
    b.extras = b.extras + extras;
    b.overs_bowled = (b.balls_bowled) / 6;
}
struct Batsman{
    char name[50];
    int balls_faced;
    int runs_scored;
};
struct Batsman b1;
/*@
    requires 0<=runs<7 && 0 <= b1.balls_faced <= 300 && 0<=b1.runs_scored <= 1800;
    ensures b1.balls_faced == \old(b1.balls_faced)+1;
    ensures b1.runs_scored == \old(b1.runs_scored) + runs;
*/
void update_batsman(int runs){
    b1.balls_faced ++;
    b1.runs_scored = b1.runs_scored + runs;
}
struct Player{
    char name[60];
    int age;
    int num_matches;
    float batting_average;
    float bowling_average;
    int right_handed;
};
struct Player p;
/*@

    requires 0 <= batting_average <= 100;
    requires 0 <= bowling_average <= 100;
    ensures p.batting_average == batting_average;
    ensures p.bowling_average == bowling_average;
*/
void update_player(float batting_average,float bowling_average){
    p.batting_average = batting_average;
    p.bowling_average = bowling_average;

}
struct Team{
    struct Player player[11];
    char team_name[30];
    char captain[30];
    int runs_scored;
    int wickets;
};
struct Team t;
/*@
    requires 0<=t.runs_scored<=10000 && 0<=t.wickets<=150;
    requires 0 <= runs <= 500 && 0<=wickets<=10 ;
    ensures t.runs_scored == \old(t.runs_scored) + runs;
    ensures t.wickets == \old(t.wickets) + wickets;
*/
void update_team(int runs,int wickets){
    t.runs_scored +=runs;
    t.wickets += wickets;
}
struct innings1{
    char playing_team[30];
    int total_runs;
    int wickets;
    int total_overs;
    int overs_completed;
    float current_runrate;
    struct Batsman striker;
    struct Batsman runner;
    struct Bowler bowler;
};
struct innings2{
    char playing_team[30];
    int total_runs;
    int target_score;
    int wickets;
    int total_overs;
    int overs_completed;
    float current_runrate;
    float required_runrate;
    struct Batsman striker;
    struct Batsman runner;
    struct Bowler bowler;
};
struct Scoreboard{
    struct Team team[2];
    struct innings1 i1;
    struct innings2 i2;
};
struct Scoreboard s;
/*@
    requires 0 <= runs <= 6 && 0<=wkt<=1 && 0<=total_balls<=350;
    requires 0<=s.i1.total_runs<=500 && 0<=s.i1.wickets <=10 && 0< s.i1.overs_completed <= 50 && 0<= s.i1.current_runrate <=8;
    ensures s.i1.total_runs == \old(s.i1.total_runs) + runs;
    ensures s.i1.wickets == \old(s.i1.wickets) + wkt;
    ensures s.i1.overs_completed == total_balls /6;
    ensures s.i1.current_runrate == (s.i1.total_runs / s.i1.overs_completed);
*/

void update_innings1(int runs,int wkt,int total_balls){
    s.i1.total_runs += runs;
    s.i1.wickets += wkt;
    s.i1.overs_completed = total_balls / 6;
    if ( s.i1.overs_completed >0){
        s.i1.current_runrate = s.i1.total_runs / s.i1.overs_completed;
    }
    else{
        s.i1.current_runrate = 0;
    }
}

/*@
    requires 0 <= runs <= 6 && 0<=wkt<=1 && 0<=total_balls<=350;
    requires 0<=s.i2.total_runs<=500 && 0<=s.i2.wickets <=10 && 0<= s.i2.overs_completed <= 50 && 0<= s.i2.current_runrate <=8 && 0<=s.i2.required_runrate<=8;
    ensures s.i2.total_runs == \old(s.i2.total_runs) + runs;
    ensures s.i2.wickets == \old(s.i2.wickets) + wkt;
    ensures s.i2.overs_completed == total_balls /6;
    ensures s.i2.current_runrate ==(s.i2.total_runs / s.i2.overs_completed);
    ensures s.i2.required_runrate == (s.i1.total_runs / s.i2.overs_completed);
*/
void update_innings2(int runs,int wkt,int total_balls){
    s.i2.total_runs += runs;
    s.i2.wickets += wkt;
    s.i2.overs_completed = total_balls / 6;
    s.i2.current_runrate = s.i2.total_runs / s.i2.overs_completed;
    s.i2.required_runrate = s.i1.total_runs / s.i2.overs_completed;
};

/*@
    requires 0 <= runs <= 6 && 0<=wkt<=1 && 0<=total_balls<=350;
    requires 1<=innings<=2;
    behavior one:
        assumes innings == 1;
        ensures \result == 1;
    behavior two:
        assumes innings ==2;
        ensures \result ==2;
    disjoint behaviors;
    complete behaviors;
*/
int update_scorecard(int innings,int runs,int wkt,int total_balls){
    if (innings ==1){
        update_innings1(runs,wkt,total_balls);
        return 1;
    }
    else{
        update_innings2(runs,wkt,total_balls);
        return 2;
    }
}

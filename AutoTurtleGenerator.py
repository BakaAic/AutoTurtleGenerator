from tkinter import *
from tkinter.ttk import *
from tkinter import messagebox
try:
    from PIL import Image, ImageTk
except ImportError:
    import pip
    pip.main(['install', 'pillow'])
    from PIL import Image, ImageTk
try:
    import windnd
except ImportError:
    import pip
    pip.main(['install', 'windnd'])
    import windnd
import itertools
import turtle
import os,time
import math
import random

class _Picture:
    def __init__(self, path,size):
        self.path = path
        self.target_size=size
        self.image = Image.open(path).convert('RGBA')
        self.width = self.image.width
        self.height = self.image.height
        self.sizeChange()
        self.getDeviation()
        self.origin_tkImage = ImageTk.PhotoImage(self.image)
        self.tkImage = ImageTk.PhotoImage(self.image)
        self.modifiedImg = self.image.copy()
        
    def getModifiedData(self):
        return self.modifiedImg.load()
        
    def getTkImage(self,_img):
        return ImageTk.PhotoImage(_img)
    
    def sizeChange(self):
        if self.width>self.height:
            self.image = self.image.resize((self.target_size[0],int(self.height*self.target_size[0]/self.width)),Image.Resampling.LANCZOS)
        else: 
            self.image = self.image.resize((int(self.width*self.target_size[1]/self.height),self.target_size[1]),Image.Resampling.LANCZOS)
        self.width = self.image.width
        self.height = self.image.height

    def getDeviation(self):
        self.width_deviation = (self.target_size[0]-self.width)//2
        self.height_deviation = (self.target_size[1]-self.height)//2

    def colorLayered(self,span,deviation):
        imagedata=self.image.load()
        spanGroup=self.getSpanGroup(span,deviation)
        _seq=[]
        for y in range(self.height):
            for x in range(self.width):
                _r, _g, _b, _T = imagedata[x, y]
                _seq.append((self.getClosestSpan(spanGroup,_r),self.getClosestSpan(spanGroup,_g),self.getClosestSpan(spanGroup,_b),255))
        self.modifiedImg=Image.new('RGBA',(self.width,self.height))
        self.modifiedImg.putdata(_seq)
        self.tkImage = self.getTkImage(self.modifiedImg)
        return len(set(_seq))
                
    def getClosestSpan(self,spanGroup,num):
        assert num>=0 and num<=255, 'num must be in range(0,256)'
        for i in range(len(spanGroup)):
            if num>=spanGroup[i][0] and num<=spanGroup[i][1]:
                if spanGroup[i][0]-num>=num-spanGroup[i][1]:
                    return spanGroup[i][0]
                else:
                    return spanGroup[i][1]
        
    def getSpanGroup(self,span,deviation):
        assert span>=1 and span<=255, 'span must be in range(0,256)'
        assert deviation>=0 and deviation<=255, 'deviation must be in range(0,256)'
        spanGroup=[]
        if deviation!=0:
            spanGroup.append((0,deviation))
            deviation+=1
        for i in range(0+deviation,256+2*span+deviation,span):
            if i<=255:
                if i+span-1<=255:
                    spanGroup.append((i,i+span-1))
                else:
                    spanGroup.append((i,255))
            else:
                break
        return spanGroup

class Tool:
    @staticmethod
    def colorTrans(color):
        rgb='#'+hex(color[0])[2:].zfill(2).upper()+hex(color[1])[2:].zfill(2).upper()+hex(color[2])[2:].zfill(2).upper()
        return rgb
        
class Outline:
    def __init__(self,pos):
        self.lines=[pos]
        self.connectArea=[]
        self.posArea(pos)
        self.dead=False
    def __iter__(self):
        return iter(self.lines)
    def __getitem__(self,index):
        return self.lines[index]
    def __len__(self):
        return len(self.lines)
    def __str__(self):
        return str(self.lines)
    def __repr__(self):
        return str(self.lines)
    def die(self):
        self.dead=True
    def posArea(self,pos):
        self.connectArea.extend([(pos[0],pos[1]-1),(pos[0],pos[1]+1),(pos[0]-1,pos[1]),(pos[0]+1,pos[1]),(pos[0]-1,pos[1]-1),(pos[0]-1,pos[1]+1),(pos[0]+1,pos[1]-1),(pos[0]+1,pos[1]+1)])
    def add(self,pos):
        self.lines.append(pos)
        self.posArea(pos)
    def addline(self,line):
        for p in line:
            self.add(p)
    def getConnectArea(self):
        return set(self.connectArea)
    def isConnect(self,pos):
        return pos in self.getConnectArea()
    def lineSet(self):
        return set(self.lines)
    def connectCompare(self,outline):
        if id(self)==id(outline):
            return 0
        if outline.dead:
            return 0
        return len(self.getConnectArea()&outline.lineSet())
            
            
class PixelGroup:
    def __init__(self,pos,color,boundary):
        self.PixelBox=[pos] #实际像素坐标
        self.decareBox={pos[0]:{pos[1]}}   #实际像素坐标区域
        self.color=color
        self.rgb=Tool.colorTrans(color)
        self.level=1    #层级
        self.boundary=boundary
        self.virtualArea={} #虚拟像素坐标区域集合
        self.virtualSize=0  #虚拟像素坐标区域大小
        self.AreaBox_X={}
        self.AreaBox_Y={}
        self.outline=[] #轮廓
        #=================#
        self.grandFather=[]
        self.father=[]
        self.son=[]
        self.grandSon=[]
        self.fellow=[]
        
    def add(self,pos):
        self.PixelBox.append(pos)
        
    def isGroup(self,color,near=1):
        if self.color[0] in range(color[0]-near,color[0]+near+1) and self.color[1] in range(color[1]-near,color[1]+near+1) and self.color[2] in range(color[2]-near,color[2]+near+1):
            return True
        return False
    
    def inGroup(self,pos):
        return pos in self.PixelBox
    
    def sameSeniority(self,group):
        self.fellow.append(group)
    
    def _elementMapping(self):
        self.mapping=[]
        for i in self.PixelBox:
            self.mapping.append(hash(i))
    
    def getOutline(self):
        #获得了轮廓，但未分出外轮廓
        self._Boundary=self._getMaxBoundary()
        _outlineX=[]
        _outlineY=[]
        for x in range(self._Boundary[0],self._Boundary[1]+1):
            for y in range(self._Boundary[2],self._Boundary[3]+1):
                if x in self.AreaBox_Y[y] and y in self.AreaBox_X[x]:
                    if x-1 not in self.AreaBox_Y[y] or x+1 not in self.AreaBox_Y[y]:
                        _outlineX.append((x,y))
        for x in range(self._Boundary[0],self._Boundary[1]+1):
            for y in range(self._Boundary[2],self._Boundary[3]+1):
                if x in self.AreaBox_Y[y] and y in self.AreaBox_X[x]:
                    if y-1 not in self.AreaBox_X[x] or y+1 not in self.AreaBox_X[x]:
                        _outlineY.append((x,y))
        self.outline=list(set(_outlineX)|set(_outlineY))
    
    def outerOutlineStrip(self):
        #去除内轮廓
        if len(self.outline)<=12:
            return
        _outlineGroup=[]
        for pos in self.outline:
            if _outlineGroup==[]:
                _outlineGroup.append(Outline(pos))
                continue
            _addlines=None
            _deleteline=[]
            for outlines in _outlineGroup:
                if _addlines==None:
                    if outlines.isConnect(pos):
                        outlines.add(pos)
                        _addlines=outlines
                        continue
                else:
                    if outlines.isConnect(pos):
                        _addlines.addline(outlines)
                        _deleteline.append(outlines)
            else:
                _outlineGroup.append(Outline(pos))
                             
            for lines in _deleteline:
                _outlineGroup.remove(lines)
                
        _outlineGroup.sort(key=lambda x:len(x),reverse=True)
        _delete=[]
        for outlines1,outlines2 in itertools.combinations(_outlineGroup,2):
            if outlines1.connectCompare(outlines2):
                outlines1.addline(outlines2)
                outlines2.die()
                _delete.append(outlines2)
        for outlines in _delete:
            _outlineGroup.remove(outlines)
            
        max_min_list=self._getOutlineMaxMin(_outlineGroup)
        
        for lines in _outlineGroup:
            if max_min_list[0] in [i[0] for i in lines] and max_min_list[1] in [i[0] for i in lines] and max_min_list[2] in [i[1] for i in lines] and max_min_list[3] in [i[1] for i in lines]:
                self.outline=list(lines)
                break
        self.outline=list(set(self.outline))
            
    def _isConnect(self,line1,line2):
        for p in line1:
            if self._posNear(p,line2):
                return True
        return False
            
        
    def _getOutlineMaxMin(self,lines):
        _All_X=[]
        _All_Y=[]
        for line in lines:
            for p in line:
                _All_X.append(p[0])
                _All_Y.append(p[1])
        return (min(_All_X),max(_All_X),min(_All_Y),max(_All_Y))
        
        
    def _posNear(self,pos,line):
        Octopus=((pos[0]+1,pos[1]),(pos[0]+1,pos[1]+1),(pos[0],pos[1]+1),(pos[0]-1,pos[1]+1),(pos[0]-1,pos[1]),(pos[0]-1,pos[1]-1),(pos[0],pos[1]-1),(pos[0]+1,pos[1]-1))
        
        for p in Octopus:
            if p in line:
                return True
        return False
        
    def lowerSeniority(self,group):
        self.levelUp()
        if self.father:
            if group.level<self.father[0].level:
                self.grandFather.append(self.father[0])
                self.father=[group]
            else:
                self.grandFather.append(group)
        else:
            self.father.append(group)
        for i in self.son:
            i.lowerSeniority(group)
        
    def higherSeniority(self,group):
        for i in self.son:
            if group in i.father:
                self.grandSon.append(i)
                self.son.remove(i)
                group.higherSeniority(i)
            elif group in i.son:
                self.grandSon.append(group)
            else:
                self.son.append(group)

    def levelUp(self):
        self.level+=1
    
    def relationship(self,group):
        if group in self.father or group in self.son or group in self.fellow or group in self.grandFather or group in self.grandSon:
            return True
        else:
            return False
            
    def initAreaBox(self):
        for p in self.PixelBox:
            if p[0] in self.AreaBox_X:
                self.AreaBox_X[p[0]][p[1]]=1
            else:
                self.AreaBox_X[p[0]]={p[1]:1}
            if p[1] in self.AreaBox_Y:
                self.AreaBox_Y[p[1]][p[0]]=1
            else:
                self.AreaBox_Y[p[1]]={p[0]:1}
    
    def _getMaxBoundary(self):
        _x=[]
        _y=[]
        for i in self.PixelBox:
            _x.append(i[0])
            _y.append(i[1])
        return (min(_x),max(_x),min(_y),max(_y))

    def getStartPos(self):
        _x=min(self.AreaBox_X.keys())
        _y=min(self.AreaBox_X[_x].keys())
        return (_x,_y)
        
    def isBoundary(self,pos):
        if pos[0] == max(self.AreaBox_Y[pos[1]]) or pos[0] == min(self.AreaBox_Y[pos[1]]):
            return 1
        if pos[1] == max(self.AreaBox_X[pos[0]]) or pos[1] == min(self.AreaBox_X[pos[0]]):
            return 1
        return 0
        
        
    def getVirtualArea(self):
        _virtualAreaX=[]
        _virtualAreaY=[]
        for y in range(self._Boundary[2],self._Boundary[3]+1):
            for x in range(self._Boundary[0],self._Boundary[1]+1):
                if x>=min(self.AreaBox_Y[y]) and x<=max(self.AreaBox_Y[y]):
                    _virtualAreaX.append((x,y))
        for x in range(self._Boundary[0],self._Boundary[1]+1):
            for y in range(self._Boundary[2],self._Boundary[3]+1):
                if y>=min(self.AreaBox_X[x]) and y<=max(self.AreaBox_X[x]):
                    _virtualAreaY.append((x,y))
        self.virtualArea=set(_virtualAreaX)&set(_virtualAreaY)
        self.virtualSize=len(self.virtualArea)
        
            
class PixelManager:
    def __init__(self,width,height,imgdata,root):
        self.size_w=width
        self.size_h=height
        self.imgdata=imgdata
        self.GroupList=[]
        self.GroupPos={}
        self.VirtualPos={}
        self.GroupCount=0
        self.root=root
    def shuffleGroup(self):
        random.shuffle(self.GroupList)
            
    def processWindow(self,pos=None,mid=False):
        self.process_W=Toplevel(self.root)
        self.process_W.attributes('-topmost',1)
        self.process_W.title('Processing')
        if mid:
                self.process_W.geometry(f'235x85+{self.root.winfo_screenwidth()//2-117}+{self.root.winfo_screenheight()//2-42}')
        else:
            if pos:
                self.process_W.geometry('235x85+{}+{}'.format(pos[0],pos[1]))
            else:
                self.process_W.geometry('235x85')
        self.process_W.resizable(0,0)
        self._Label_process=Label(self.process_W,text='Processing...0/0')
        self._Label_process.place(anchor=CENTER,relx=0.5,rely=0.5)
        
    def process(self,step,total_step,current,total,info=None):
        if info:
            self._Label_process.config(text='Processing...({}/{})\n{}/{}\n{}'.format(step,total_step,current,total,info))
        else:
            self._Label_process.config(text='Processing...({}/{})\n{}/{}'.format(step,total_step,current,total))
        self.process_W.update()
        
    def timeStatistical(self,timeStr):
        self._Label_process.config(text='任务已完成!\n用时{}'.format(timeStr))
        self.process_W.update()
        
    def processEnd(self):
        self.process_W.destroy()
        
    def getMaxLevel(self):
        _maxLevel=0
        for g in self.GroupList:
            if g.level>_maxLevel:
                _maxLevel=g.level
        return _maxLevel
        
    def groupGetOutline(self):
        change_count=1
        current_count=1
        self.process(2,4,round(current_count/self.GroupCount*100,2),'100%','确定像素组轮廓')
        for g in self.GroupList:
            if change_count==10:
                self.process(2,4,round(current_count/self.GroupCount*100,2),'100%','确定像素组轮廓')
                change_count=0
            change_count+=1
            current_count+=1
            g.initAreaBox()
            g.getOutline()
            g.outerOutlineStrip()
        
    def grouping(self):
        self.processWindow()
        for y in range(self.size_h):
            for x in range(self.size_w):
                if x>=1:
                    if self.GroupPos[x-1,y].isGroup(self.imgdata[x,y]):
                        self.GroupPos[x-1,y].add((x,y))
                        self.GroupPos[x,y]=self.GroupPos[x-1,y]
                        continue
                if y>=1:
                    if self.GroupPos[x,y-1].isGroup(self.imgdata[x,y]):
                        self.GroupPos[x,y-1].add((x,y))
                        self.GroupPos[x,y]=self.GroupPos[x,y-1]
                        continue
                # if x>=1 and y>=1:
                #     if self.GroupPos[x-1,y-1].isGroup(self.imgdata[x,y]):
                #         self.GroupPos[x-1,y-1].add((x,y))
                #         self.GroupPos[x,y]=self.GroupPos[x-1,y-1]
                #         continue
                # if x<=self.size_w-2 and y>=1:
                #     if self.GroupPos[x+1,y-1].isGroup(self.imgdata[x,y]):
                #         self.GroupPos[x+1,y-1].add((x,y))
                #         self.GroupPos[x,y]=self.GroupPos[x+1,y-1]
                #         continue
                    
                self.GroupList.append(PixelGroup((x,y),self.imgdata[x,y],(self.size_w,self.size_h)))
                self.GroupPos[x,y]=self.GroupList[-1]
        _tmpdel=[]
        current_count=1
        total_count=self.size_w*self.size_h
        change_count=1
        self.process(1,4,round(current_count/total_count*100,2),'100%','整理像素组')
        for y in range(self.size_h-1,-1,-1):
            for x in range(self.size_w-1,-1,-1):
                change_count+=1
                if change_count==1000:
                    self.process(1,4,round(current_count/total_count*100,2),'100%','整理像素组')
                    change_count=0
                if x>=1:
                    if self.GroupPos[x-1,y] != self.GroupPos[x,y]:
                        if self.GroupPos[x-1,y].isGroup(self.GroupPos[x,y].color):
                            _tmpdel.append(self.GroupPos[x-1,y])
                            self.groupMerge(self.GroupPos[x-1,y],self.GroupPos[x,y])
                            continue
                if y>=1:
                    if self.GroupPos[x,y-1] != self.GroupPos[x,y]:
                        if self.GroupPos[x,y-1].isGroup(self.GroupPos[x,y].color):
                            _tmpdel.append(self.GroupPos[x,y-1])
                            self.groupMerge(self.GroupPos[x,y-1],self.GroupPos[x,y])
                            continue
                # if x>=1 and y>=1:
                #     if self.GroupPos[x-1,y-1] != self.GroupPos[x,y]:
                #         if self.GroupPos[x-1,y-1].isGroup(self.GroupPos[x,y].color):
                #             _tmpdel.append(self.GroupPos[x-1,y-1])
                #             self.groupMerge(self.GroupPos[x-1,y-1],self.GroupPos[x,y])
                #             continue
                # if x<=self.size_w-2 and y>=1:
                #     if self.GroupPos[x+1,y-1] != self.GroupPos[x,y]:
                #         if self.GroupPos[x+1,y-1].isGroup(self.GroupPos[x,y].color):
                #             _tmpdel.append(self.GroupPos[x+1,y-1])
                #             self.groupMerge(self.GroupPos[x+1,y-1],self.GroupPos[x,y])
                #             continue
                current_count+=1
        
        _tmpdel=list(set(_tmpdel))
        for g in _tmpdel:
            self.GroupList.remove(g)
                
        self.GroupCount=len(self.GroupList)
        
    def groupMerge(self,group1,group2):
        _tmp=[]
        
        for p in self.GroupPos:
            if self.GroupPos[p]==group1:
                _tmp.append(p)
        for p in _tmp:
            self.GroupPos[p]=group2
        for _d in group1.PixelBox:
            group2.add(_d)

    def groupLevelJudge(self):
        change_count=1
        current_count=1
        self.process(3,4,round(current_count/self.GroupCount*100,2),'100%','像素组分级准备')
        for g in self.GroupList:
            if change_count==10:
                self.process(3,4,round(current_count/self.GroupCount*100,2),'100%','像素组分级准备')
                change_count=0
            change_count+=1
            current_count+=1
            g.getVirtualArea()
            for p in g.virtualArea:
                if p not in self.VirtualPos:
                    self.VirtualPos[p]=[g]
                else:
                    self.VirtualPos[p].append(g)
        change_count=1
        current_count=1
        total_count=len(self.VirtualPos)
        self.process(4,4,round(current_count/total_count*100,2),'100%','像素组对比评级')
        for v in self.VirtualPos:
            if change_count==1000:
                self.process(4,4,round(current_count/total_count*100,2),'100%','像素组对比评级')
                change_count=0
            change_count+=1
            current_count+=1
            if len(self.VirtualPos[v])>1:
                self.quickcompare(self.VirtualPos[v])
        
        self.processEnd()
        
        # self.tstlevel=Toplevel()
        # self.tstlevel.title('测试')
        # self.tstlevel.geometry('800x800')
        # self.tstlevel.resizable(0,0)
        # tstBoard=Canvas(self.tstlevel,width=800,height=800,bg='white')
        # tstBoard.pack()

        # n=0
        # for g in self.GroupList:
        #     n+=1
        #     if n in [3]:
        #     # if g.level==curLevel:
        #         # print(len(g.PixelBox))
        #         # for p in g.PixelBox:
        #         #     tstBoard.create_line(p[0],p[1],p[0]+1,p[1]+1,fill=g.rgb)
        #         # print(len(g.outline))
        #         print(len(set(g.outline)))
        #         print(g.rgb)
        #         g.rgb='#FF0000'
        #         print(g.outline)
        #         for p in g.outline:
        #             tstBoard.create_line(p[0],p[1],p[0]+1,p[1]+1,fill='red')
        #     else:
        #         for p in g.PixelBox:
        #             tstBoard.create_line(p[0],p[1],p[0]+1,p[1]+1,fill=g.rgb)

                
    def quickcompare(self,_grouplist):
        if len(_grouplist)==2:
            if _grouplist[0].relationship(_grouplist[1]) or _grouplist[1].relationship(_grouplist[0]):
                return
            _result=self.compare(_grouplist[0],_grouplist[1])
            if _result:
                _result[0].higherSeniority(_result[1])
                _result[1].lowerSeniority(_result[0])
            else:
                _grouplist[0].sameSeniority(_grouplist[1])
                _grouplist[1].sameSeniority(_grouplist[0])
        else:
            for _couple in itertools.combinations(_grouplist,2):
                if _couple[0].relationship(_couple[1]) or _couple[1].relationship(_couple[0]):
                    continue
                _result=self.compare(_couple[0],_couple[1])
                if _result:
                    _result[0].higherSeniority(_result[1])
                    _result[1].lowerSeniority(_result[0])
                else:
                    _couple[0].sameSeniority(_couple[1])
                    _couple[1].sameSeniority(_couple[0])
                
    def compare(self,g1,g2):
        if g1.virtualSize>g2.virtualSize:
            groupBig=g1
            groupSmall=g2
        elif g1.virtualSize<g2.virtualSize:
            groupBig=g2
            groupSmall=g1
        else:
            return None
        if groupBig.virtualSize>groupSmall.virtualSize:
            if len(groupSmall.virtualArea-groupBig.virtualArea)==0:
                _boundarycount=0
                for p in groupSmall.virtualArea:
                    _boundarycount+=groupBig.isBoundary(p)
                if _boundarycount==0:
                    return (groupBig,groupSmall)
        return None
            
class AutoTurtleGenerator:
    def __init__(self,randomGroup=False):
        self.Picture=None
        self.imgFile=None
        self.span=10    #色彩分辨率 10-255
        self.deviation=0    #色彩偏移 0-255
        self.colorNum=0
        self.RunFlag=False
        self.Manager=None
        self.turtleHandle=None
        self.randomGroup=randomGroup
        
    def main(self):
        self.buildWindow()
        
    def dropFile(self,file):
        if not self.RunFlag:
            self.imgFile=file[-1].decode('gb2312')
            if self.imgFile.split('.')[-1] not in ['png','jpg','jpeg','bmp']:
                self.errorShow('Only support png,jpg,jpeg,bmp')
                return
            if self.Picture!=None:
                self.Picture.image.close()
                self._Canvas_origin.delete('textTags')
                self._Canvas_origin.delete('originPic')
                self._Canvas_Modified.delete('modifiedPic')
            try:
                self.Picture=_Picture(self.imgFile,(400,400))
            except:
                self.errorShow('Open file error')
                return
            self._Canvas_origin.create_image(2+self.Picture.width_deviation,2+self.Picture.height_deviation,anchor=NW,image=self.Picture.origin_tkImage,tag='originPic')
            self.colorNum=self.Picture.colorLayered(self.span,self.deviation)
            self._Frame_Control['text']='调整 色彩数量: '+str(self.colorNum)
            self._Canvas_Modified.create_image(2+self.Picture.width_deviation,2+self.Picture.height_deviation,anchor=NW,image=self.Picture.tkImage,tag='modifiedPic')
            self.ButtonABLE()
        
    def errorShow(self,info):
        messagebox.showerror('Error',info)
        
    def spanChange(self,event):
        self.span=int(float(event))
        if self._Scale_span.get()!=self.span:
            self._Scale_span.set(self.span)
        self._Label_span['text']='色彩分辨率: '+str(self.span)
            
    def spanChangeTo(self,event):
        if self.Picture:
            self.colorNum=self.Picture.colorLayered(self.span,self.deviation)
            self._Frame_Control['text']='调整 色彩数量: '+str(self.colorNum)
            self._Canvas_Modified.delete('modifiedPic')
            self._Canvas_Modified.create_image(2+self.Picture.width_deviation,2+self.Picture.height_deviation,anchor=NW,image=self.Picture.tkImage,tag='modifiedPic')
        
    def deviationChange(self,event):
        self.deviation=int(float(event))
        if self._Scale_deviation.get()!=self.deviation:
            self._Scale_deviation.set(self.deviation)
        self._Label_deviation['text']='色彩偏移: '+str(self.deviation)
    
    def deviationChangeTo(self,event):
        if self.Picture:
            self.colorNum=self.Picture.colorLayered(self.span,self.deviation)
            self._Frame_Control['text']='调整 色彩数量: '+str(self.colorNum)
            self._Canvas_Modified.delete('modifiedPic')
            self._Canvas_Modified.create_image(2+self.Picture.width_deviation,2+self.Picture.height_deviation,anchor=NW,image=self.Picture.tkImage,tag='modifiedPic')
        
    def ButtonABLE(self):
        if self.Picture:
            self._Button_Run['state']=NORMAL
        else:
            self._Button_Run['state']=DISABLED
    
    def buildWindow(self):
        self.root=Tk()
        self.root.title('AutoTurtleGenerator')
        self.root.geometry('900x650')
        self.root.resizable(0,0)
        
        self.turtleRecord=TurtleRecord(self.root)
        
        _Frame_origin=LabelFrame(self.root,text='原始图像',width=430,height=430)
        _Frame_origin.place(anchor=CENTER,relx=0.5,rely=0.5,x=-220,y=-100)
        self._Canvas_origin=Canvas(_Frame_origin,width=400,height=400,background='black')
        self._Canvas_origin.place(anchor=CENTER,relx=0.5,rely=0.5)
        self._Canvas_origin.create_text(200,200,text='拖动图片到此处',tag='textTags',fill='white')
        windnd.hook_dropfiles(self._Canvas_origin,func=self.dropFile)
        _Frame_Modified=LabelFrame(self.root,text='处理后',width=430,height=430)
        _Frame_Modified.place(anchor=CENTER,relx=0.5,rely=0.5,x=220,y=-100)
        self._Canvas_Modified=Canvas(_Frame_Modified,width=400,height=400,background='black')
        self._Canvas_Modified.place(anchor=CENTER,relx=0.5,rely=0.5)
        self._Frame_Control=LabelFrame(self.root,text='调整 色彩数量: 0',width=870,height=200)
        self._Frame_Control.place(anchor=CENTER,relx=0.5,rely=0.5,x=0,y=215)
        
        self._Label_span=Label(self._Frame_Control,text='色彩分辨率: '+str(self.span))
        self._Label_span.place(anchor=CENTER,relx=0.2,rely=0.3,x=-70)
        self._Label_deviation=Label(self._Frame_Control,text='色彩偏移: '+str(self.deviation))
        self._Label_deviation.place(anchor=CENTER,relx=0.2,rely=0.6,x=-70)
        
        self._Scale_span=Scale(self._Frame_Control,from_=10,to=255,orient=HORIZONTAL,length=400,command=self.spanChange)
        self._Scale_span.place(anchor=CENTER,relx=0.5,rely=0.3,x=-50)
        self._Scale_span.bind('<ButtonRelease-1>',self.spanChangeTo)
        self._Scale_span.set(self.span)
        self._Scale_deviation=Scale(self._Frame_Control,from_=0,to=255,orient=HORIZONTAL,length=400,command=self.deviationChange)
        self._Scale_deviation.place(anchor=CENTER,relx=0.5,rely=0.6,x=-50)
        self._Scale_deviation.bind('<ButtonRelease-1>',self.deviationChangeTo)
        self._Scale_deviation.set(self.deviation)
        
        from tkinter import Button as OldButton
        self._Button_Run=OldButton(self._Frame_Control,text='开始自动化',width=20,height=5,command=self.run,state=DISABLED,relief='groove')
        self._Button_Run.place(anchor=CENTER,relx=0.8,rely=0.5,x=50)
        self.root.mainloop()

    def run(self):
        self._Scale_span['state']=DISABLED
        self._Scale_deviation['state']=DISABLED
        self._Button_Run['state']=DISABLED
        self.Manager=PixelManager(self.Picture.width,self.Picture.height,self.Picture.getModifiedData(),self.root)
        self.Manager.grouping()
        self.Manager.groupGetOutline()
        self.Manager.groupLevelJudge()
        self.turtleHandle=TurtleWorks(self.Manager,self.turtleRecord,randomGroup=self.randomGroup)
        self.turtleRecord.picAdjustArguments(self.span,self.deviation)
        self.turtleHandle.work()
        
class TurtleRecord:
    def __init__(self,root):
        self.root=root
        self.saveFile=None
        self.localPath=os.getcwd()+'\\'
        self.currentName=1
        self.operationList=None
    def setOperationList(self,operationList):
        self.operationList=operationList
    def getNewName(self):
        while True:
            if os.path.exists(self.localPath+'turtle_'+str(self.currentName)+'.py'):
                self.currentName+=1
            else:
                return 'turtle_'+str(self.currentName)+'.py'
        
    def picAdjustArguments(self,span,deviation):
        self.adjustText='#span='+str(span)+',deviation='+str(deviation)+'\n'
    def setSaveFile(self,saveFile):
        self.saveFile=saveFile
    def recordWindow(self):
        self._record_top=Toplevel(self.root)
        self._record_top.title('操作记录')
        self._record_top.geometry(f'400x800+{self.root.winfo_screenwidth()-400}+0')
        self._record_top.resizable(0,0)
        self._Frame_record=LabelFrame(self._record_top,text='输出',width=390,height=790)
        self._Frame_record.place(anchor=CENTER,relx=0.5,rely=0.5)
        
        self._ListBox_record=Listbox(self._Frame_record,width=50,height=42,background='green',foreground='white',selectmode=SINGLE,relief='groove'
                                     ,selectbackground='green',selectforeground='white',activestyle='none')
        self._ListBox_record.pack(side=LEFT,fill=Y,expand=1)
        self._Scrollbar_record=Scrollbar(self._Frame_record)
        self._Scrollbar_record.pack(side=RIGHT,fill=Y)
        self._ListBox_record.config(yscrollcommand=self._Scrollbar_record.set)
        self._Scrollbar_record.config(command=self._ListBox_record.yview)
        
        
    def lengthCheck(self):
        if len(self.operationList)>=42:
            self._Scrollbar_record.pack(side=RIGHT,fill=Y)
        else:
            self._Scrollbar_record.pack_forget()
    
    def record(self,operation):
        self._ListBox_record.insert(END,operation)
        self._ListBox_record.see(END)
        self.lengthCheck()

    def addOperation(self,operation):
        self.operationList.append(operation)
        self.record(operation)
        
    def addOper(self,operation):
        self.addOperation(operation)
    
    def save(self):
        assert self.saveFile!=None,'未设置保存文件'
        with open(self.saveFile,'w') as f:
            f.write(self.adjustText+'import turtle\nimport math\n\n')
            for i in self.operationList:
                f.write(i+'\n')
                
    def bevelCalc(self,step):
        return (step)*math.sqrt(2)
    
    #=====================以下为turtle操作映射=====================#
    def setup(self,*args):
        _arg=','.join([str(i) for i in args])
        self.addOperation('turtle.setup('+_arg+')')
        turtle.setup(*args)
    def bgcolor(self,*args):
        _arg=','.join([str(i) for i in args])
        self.addOperation('turtle.bgcolor("'+_arg+'")')
        turtle.bgcolor(*args)
    def bevelset(self,*args):
        self.addOperation('bevel=math.sqrt(2)')
    def pencolor(self,*args):
        _arg=','.join([str(i) for i in args])
        self.addOperation('turtle.pencolor("'+_arg+'")')
        turtle.pencolor(*args)
    def pensize(self,*args):    
        _arg=','.join([str(i) for i in args])
        self.addOperation('turtle.pensize('+_arg+')')
        turtle.pensize(*args)
    def speed(self,*args):
        _arg=','.join([str(i) for i in args])
        self.addOperation('turtle.speed('+_arg+')')
        turtle.speed(*args)
    def pendown(self):
        self.addOperation('turtle.pendown()')
        turtle.pendown()
    def penup(self):
        self.addOperation('turtle.penup()')
        turtle.penup()
    def goto(self,*args):
        _arg=','.join([str(i) for i in args])
        self.addOperation('turtle.goto('+_arg+')')
        turtle.goto(*args)
    def fillcolor(self,*args):
        _arg=','.join([str(i) for i in args])
        self.addOperation('turtle.fillcolor("'+_arg+'")')
        turtle.fillcolor(*args)
    def begin_fill(self):
        self.addOperation('turtle.begin_fill()')
        turtle.begin_fill()
    def end_fill(self):
        self.addOperation('turtle.end_fill()')
        turtle.end_fill()
    def forward(self,*args):
        _arg=','.join([str(i) for i in args])
        self.addOperation('turtle.forward('+_arg+')')
        turtle.forward(*args)
    def forward_bevel(self,*args):
        _arg=','.join([str(i) for i in args])
        self.addOperation('turtle.forward('+_arg+'*bevel)')
        turtle.forward(self.bevelCalc(*args))
    def backward(self,*args):
        _arg=','.join([str(i) for i in args])
        self.addOperation('turtle.backward('+_arg+')')
        turtle.backward(*args)
    def left(self,*args):
        _arg=','.join([str(i) for i in args])
        self.addOperation('turtle.left('+_arg+')')
        turtle.left(*args)
    def right(self,*args):
        _arg=','.join([str(i) for i in args])
        self.addOperation('turtle.right('+_arg+')')
        turtle.right(*args)
    def seth(self,*args):
        _arg=','.join([str(i) for i in args])
        self.addOperation('turtle.seth('+_arg+')')
        turtle.seth(*args)
    def setheading(self,*args):
        _arg=','.join([str(i) for i in args])
        self.addOperation('turtle.setheading('+_arg+')')
        turtle.setheading(*args)
    def dot(self,*args):
        _arg=','.join([str(i) for i in args])
        self.addOperation('turtle.dot('+_arg+')')
        turtle.dot(*args)
    def hideturtle(self):
        self.addOperation('turtle.hideturtle()')
        turtle.hideturtle()
    def update(self):
        self.addOperation('turtle.update()')
        turtle.update()
    def done(self):
        self.addOperation('turtle.done()')
        # turtle.done()
            
class TurtleWorks:
    def __init__(self,GroupManager,record,randomGroup=False):
        self.GroupManager=GroupManager
        self.record=record
        self.record.setSaveFile(self.record.getNewName())
        self.operationList=[]
        self.record.setOperationList(self.operationList)
        self.workStartTime=time.time()
        self.author='Aikko'
        self.randomGroup=randomGroup
    def initTurtle(self):
        self.record.record('import turtle')
        self.record.setup(800,800)
        self.record.bgcolor('black') 
        self.record.bevelset()
        self.record.pensize(1)
        self.record.speed(0)
    def work(self):
        self.record.recordWindow()
        self.GroupManager.processWindow()
        self.initTurtle()
        maxLevel=self.GroupManager.getMaxLevel()
        if self.randomGroup:
            self.GroupManager.shuffleGroup()
        curCount=1
        startTime=time.time()
        _color=None
        for i in range(1,maxLevel+1):
            for group in self.GroupManager.GroupList:
                if group.level==i:
                    self.GroupManager.process(1,1,curCount,self.GroupManager.GroupCount,self.transTime(self.leftTime(startTime,curCount,self.GroupManager.GroupCount)))
                    _color=self._work_byGroup(group,_color)
                    curCount+=1
        self.record.hideturtle()
        self.record.done()
        self.record.save()
        self.GroupManager.processEnd()
        self.GroupManager.processWindow(mid=True)
        self.GroupManager.timeStatistical(self.transTime(time.time()-self.workStartTime,True))

    def leftTime(self,startTime,curCount,totalCount):
        _time=time.time()-startTime
        _leftTime=(_time/curCount)*(totalCount-curCount)
        return _leftTime
    
    def transTime(self,seconds,statistical=False):
        seconds=int(seconds)
        if statistical:
            _base_Str=''
        else:
            _base_Str='预计剩余'
        if seconds<60:
            return _base_Str+str(seconds)+'秒'
        elif seconds<3600:
            return _base_Str+str(seconds//60)+'分'+str(seconds%60)+'秒'
        else:
            return _base_Str+str(seconds//3600)+'小时'+str((seconds%3600)//60)+'分'+str((seconds%3600)%60)+'秒'
                
    def posDeviation(self,curPos):
        '''需增加拉伸补偿'''
        return (curPos[0]-200,-curPos[1]+200)
    
    def _work_byGroup(self,group,_lastColor):
        allPixel=group.PixelBox[:]
        if len(allPixel)>len(group.outline):
            _fillFlag=True
        else:
            _fillFlag=False
        _lastForward=90    #初始值
        _step=0
        _startPos=group.getStartPos()
        _footprint=[_startPos]
        self.record.penup()
        self.record.goto(*self.posDeviation(_startPos))
        if _lastColor!=group.rgb:
            self.record.pencolor(group.rgb)
        if _fillFlag:
            self.record.fillcolor(group.rgb)
            self.record.begin_fill()
        self.record.pendown()
        
        if len(allPixel)==1:
            self.record.dot(2)
            if _fillFlag:
                self.record.end_fill()
            return
        try:
            allPixel.remove(_startPos)
        except:
            pass
        _nextPos=_startPos
        if len(allPixel)==0:
            if _fillFlag:
                self.record.end_fill()
            return
        _,_lastForward=self._groupWork(group,_nextPos,_lastForward)
        self.record.seth(_lastForward)
        
        scattered=len(set(group.outline)-set(_footprint))
        _scatteredFlag=False
        while True:
            _nextPos,_nextForword=self._groupWork(group,_nextPos,_lastForward)
            _slopeFlag=False
            if _nextForword==_lastForward:
                _step+=1
            else:
                if _lastForward in [0,90,180,270]:
                    if _slopeFlag:
                        self.record.forward(_step+1)
                        _slopeFlag=False
                    else:
                        self.record.forward(_step)
                else:
                    self.record.forward_bevel(_step)
                    _slopeFlag=True
                _step=1
                self.record.seth(_nextForword)
                _lastForward=_nextForword
            try:
                allPixel.remove(_startPos)
            except:
                pass
            if _nextPos not in _footprint:
                _footprint.append(_nextPos)
            if len(set(group.outline)-set(_footprint))==0:
                #闭合
                if _fillFlag:
                    if _startPos==_nextPos:
                        _step+=1
                        break
                else:
                    _step+=1
                    break
            if not _fillFlag:
                if len(allPixel)==0:
                    if _nextForword==_lastForward:
                        _step+=1
                    break
            if _nextPos==_startPos:
                if scattered==len(set(group.outline)-set(_footprint)):
                    #主动闭合
                    _scatteredFlag=True
                    _step+=1
                    break
                else:
                    scattered=len(set(group.outline)-set(_footprint))    
                    
        if _nextForword in [0,90,180,270]:
            if _slopeFlag:
                self.record.forward(_step+1)
            else:
                self.record.forward(_step)
        else:
            self.record.forward_bevel(_step)
        if _fillFlag:
            self.record.end_fill()
        if _scatteredFlag:
            #零散点处理
            scattered_point=set(group.outline)-set(_footprint)
            for pos in scattered_point:
                self.record.penup()
                self.record.goto(*self.posDeviation(pos))
                self.record.pendown()
                self.record.dot(1) 
        return group.rgb

    def bevelCalc(self,step):
        return (step)*math.sqrt(2)
    
    def _groupWork(self,group,curPos,lastForward):
        if group.rgb=="#000000":
            pass
        nextPool=[]
        if (curPos[0]-1,curPos[1]) in group.outline:
            nextPool.append(((curPos[0]-1,curPos[1]),180))
        if (curPos[0]-1,curPos[1]-1) in group.outline:
            nextPool.append(((curPos[0]-1,curPos[1]-1),135))
        if (curPos[0],curPos[1]-1) in group.outline:
            nextPool.append(((curPos[0],curPos[1]-1),90))
        if (curPos[0]+1,curPos[1]-1) in group.outline:
            nextPool.append(((curPos[0]+1,curPos[1]-1),45))
        if (curPos[0]+1,curPos[1]) in group.outline:
            nextPool.append(((curPos[0]+1,curPos[1]),0))
        if (curPos[0]+1,curPos[1]+1) in group.outline:
            nextPool.append(((curPos[0]+1,curPos[1]+1),315)) 
        if (curPos[0],curPos[1]+1) in group.outline:
            nextPool.append(((curPos[0],curPos[1]+1),270))
        if (curPos[0]-1,curPos[1]+1) in group.outline:
            nextPool.append(((curPos[0]-1,curPos[1]+1),225))
        nextPos,nextForward=self._getMinAngle(lastForward,nextPool)
        return nextPos,nextForward
    
    def _getMinAngle(self,oldAngle,pool):
        assert len(pool)>0,'pool is empty'
        minAngle=999
        for pos,angle in pool:        
            angleDiff=self.__calcAngleDiff(oldAngle,angle)
            if angleDiff<minAngle:
                minAngle=angleDiff
                nextPos=pos
                nextAngle=angle
        return nextPos,nextAngle

    def __calcAngleDiff(self,angle1,angle2):
        diff=angle2-angle1
        if diff>=0:
            if diff-180>=0:
                diff-=360
        else:
            if diff+180<0:
                diff+=360
        return -diff+180
    

if __name__=='__main__':
    Auto=AutoTurtleGenerator(False)
    #AutoTurtleGenerator类参数为True时，绘图时会打乱Group顺序，按照层级随机进行不同坐标的绘制，为False时按照Group原始顺序，从左上到右下的优先顺序进行绘制
    Auto.main()
